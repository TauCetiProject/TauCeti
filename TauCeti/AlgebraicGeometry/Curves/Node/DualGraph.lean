/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.Node.Blowup
public import TauCeti.AlgebraicGeometry.Curves.Node.Components
import Mathlib.RingTheory.Etale.Field
import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic

/-!
# The dual graph of a geometric nodal curve

Let `X` be a proper connected nodal curve over a separably closed field `K`
(`AtWorstNodalOfRelativeDimensionOne`), and let `ν : Bl X ⟶ X` be the blowup of `X` along
`Sing(X/K)`. Given smooth marked points `p : ι → (X ↘ Spec (.of K)).smoothLocus`, this file
constructs the combinatorial dual graph `X.markedDualGraph K hnodal p : DualGraph ι` (and its
unmarked specialization `X.dualGraph K hnodal`), proves choice-free geometric characterizations of
its incidences, valences, vertex/edge counts, rational tails (`Scheme.IsRationalTail`), and
rational bridges (`Scheme.IsRationalBridge`), computes the dual graph in the smooth case, and
constructs canonical `DualGraph.Iso` isomorphisms under curve isomorphisms and extensions of
separably closed fields (`markedDualGraphBaseChangeIso`, `markedDualGraphIsoOfOverIso`).

## References

* [The Stacks Project, Tags 0C46, 0C58, 0E6X, and 0E73](https://stacks.math.columbia.edu/tag/0C46)
* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*, Ch. X.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Set TauCeti TauCeti.AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

/-! ### Finite étale schemes over fields and separably closed fields -/

section FiniteEtalePoints

/-- A finite étale scheme over a field has finitely many underlying points. -/
theorem finite_of_isFinite_of_etale {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of K)) [IsFinite f] [Etale f] : Finite Y := by
  obtain ⟨A, ⟨e⟩⟩ := f.exists_finiteEtale_algebra
  have := Algebra.FormallyUnramified.finite_of_free K A.obj
  have : IsArtinianRing A.obj := isArtinian_of_tower K inferInstance
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact e.hom.left.homeomorph.finite_iff.mp (inferInstanceAs (Finite (PrimeSpectrum A.obj)))

/-- Over a separably closed field `K`, the number of points of a finite étale `K`-scheme equals its
rank over `Spec K`. -/
theorem Hom.natCard_of_isFinite_of_etale_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K)) [IsFinite f] [Etale f] (s : Spec (.of K)) :
    Nat.card Y = f.finrank s := by
  obtain ⟨A, ⟨e⟩⟩ := f.exists_finiteEtale_algebra
  have := Algebra.FormallyUnramified.finite_of_free K A.obj
  have : IsArtinianRing A.obj := isArtinian_of_tower K inferInstance
  let _ := Fintype.ofFinite (PrimeSpectrum A.obj)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hrank : f.finrank s = Module.finrank K A.obj := by
    have hw : e.hom.left ≫ f = Spec.algebraMap K A.obj := Over.w e.hom
    rw [← Scheme.Hom.finrank_comp_left_of_isIso e.hom.left f, hw, Spec.algebraMap]
    exact (Scheme.Hom.finrank_SpecMap_algebraMap K A.obj s).trans
      (congrFun Module.rankAtStalk_eq_finrank_of_free s)
  have hcard : Nat.card (PrimeSpectrum A.obj) = Module.finrank K A.obj := by
    rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed K A.obj).toLinearEquiv.finrank_eq,
      Module.finrank_pi, Nat.card_eq_fintype_card]
  exact (Nat.card_congr e.hom.left.homeomorph.toEquiv.symm).trans (hcard.trans hrank.symm)

/-- Base-changing a finite étale scheme across an extension of separably closed fields induces a
bijection on underlying points. -/
theorem bijective_of_isPullback_of_isFinite_of_etale {K L : Type u} [Field K] [IsSepClosed K]
    [Field L] [IsSepClosed L] [Algebra K L] {Y Y' : Scheme.{u}}
    {f : Y ⟶ Spec (.of K)} {f' : Y' ⟶ Spec (.of L)} {g : Y' ⟶ Y} [IsFinite f] [Etale f]
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    Function.Bijective g := by
  have : IsFinite f' := MorphismProperty.of_isPullback H ‹_›
  have : Etale f' := MorphismProperty.of_isPullback H ‹_›
  have : Finite Y' := finite_of_isFinite_of_etale f'
  have : Surjective g := MorphismProperty.of_isPullback H.flip inferInstance
  refine (Nat.bijective_iff_surjective_and_card g).mpr ⟨g.surjective, ?_⟩
  let ptL : Spec (.of L) := IsLocalRing.closedPoint L
  rw [f'.natCard_of_isFinite_of_etale_of_isSepClosed ptL,
    f.natCard_of_isFinite_of_etale_of_isSepClosed
      (Spec.map (CommRingCat.ofHom (algebraMap K L)) ptL)]
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ H ptL

end FiniteEtalePoints

/-! ### Fibers and image of the branch scheme -/

section BranchScheme

variable {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
  [Flat (X ↘ Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [PureRelativeDimension 1 (X ↘ Spec (.of R))]

/-- The morphism from the branch scheme into the singular-locus blowup is a closed immersion. -/
instance isClosedImmersion_branchSchemeToBlowup : IsClosedImmersion (X.branchSchemeToBlowup R) :=
  MorphismProperty.of_isPullback (X.isPullback_branchScheme R) inferInstance

/-- The image of the branch scheme in `Bl X` is the preimage of the singular locus. -/
theorem range_branchSchemeToBlowup :
    Set.range (X.branchSchemeToBlowup R) =
      (X.singularLocus R).blowupToBase ⁻¹' (X.singularLocus R).support := by
  simpa [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] using
    image_preimage_eq_of_isPullback (X.isPullback_branchScheme R) Set.univ

/-- `branchSchemeToBlowup` maps the branch fiber over `s` onto the blowup fiber over `s`. -/
theorem image_branchSchemeToBlowup_preimage_singleton (s : (X.singularLocus R).subscheme) :
    X.branchSchemeToBlowup R '' (X.branchSchemeToSingularLocus R ⁻¹' {s}) =
      (X.singularLocus R).blowupToBase ⁻¹' {(X.singularLocus R).subschemeι s} := by
  simpa using image_preimage_eq_of_isPullback (X.isPullback_branchScheme R) {s}

end BranchScheme

section NodalBranches

variable {K : Type u} [Field K] [IsSepClosed K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

private theorem isSepClosed_of_ringEquiv {k₁ k₂ : Type*} [Field k₁] [Field k₂]
    [IsSepClosed k₁] (e : k₁ ≃+* k₂) : IsSepClosed k₂ :=
  ⟨fun p hp ↦ by
    have h := IsSepClosed.splits_domain (f := (e : k₁ →+* k₂)) (p.map (e.symm : k₂ →+* k₁)) hp.map
    rwa [Polynomial.map_map, show (e : k₁ →+* k₂).comp (e.symm : k₂ →+* k₁) = .id k₂ by ext; simp,
      Polynomial.map_id] at h⟩

private theorem isSepClosed_residueField_of_etale {S : Scheme.{u}} (h : S ⟶ Spec (.of K))
    [Etale h] (s : S) : IsSepClosed (S.residueField s) := by
  let k₀ := (Spec (.of K)).residueField (h s)
  let : Algebra k₀ (S.residueField s) := (h.residueFieldMap s).hom.toAlgebra
  have : IsSepClosed k₀ := isSepClosed_of_ringEquiv
    (Scheme.Spec.residueFieldIsoOfField (h s)).symm.commRingCatIsoToRingEquiv
  exact isSepClosed_of_ringEquiv
    (RingEquiv.ofBijective _ (IsSepClosed.algebraMap_bijective k₀ (S.residueField s)))

variable (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))

/-- Over a separably closed field `K`, the fiber of `branchSchemeToSingularLocus` over every node
has cardinality `2`. -/
theorem natCard_preimage_branchSchemeToSingularLocus
    (s : (letI := hnodal.syntomic; (X.singularLocus K).subscheme)) :
    letI := hnodal.syntomic; Nat.card (X.branchSchemeToSingularLocus K ⁻¹' {s}) = 2 := by
  have := hnodal.syntomic; have := X.etale_singularLocus_subschemeι_comp hnodal
  have := isSepClosed_residueField_of_etale ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))) s
  let p := X.branchSchemeToSingularLocus K
  have := X.isFinite_branchSchemeToSingularLocus hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  have hsq : IsPullback (p.fiberι s) (p.fiberToSpecResidueField s) p
      ((X.singularLocus K).subscheme.fromSpecResidueField s) := IsPullback.of_hasPullback _ _
  have : IsFinite (p.fiberToSpecResidueField s) := MorphismProperty.of_isPullback hsq ‹_›
  have : Etale (p.fiberToSpecResidueField s) := MorphismProperty.of_isPullback hsq ‹_›
  let pt : Spec ((X.singularLocus K).subscheme.residueField s) := IsLocalRing.closedPoint _
  rw [← Nat.card_congr (p.fiberHomeo s).toEquiv,
    (p.fiberToSpecResidueField s).natCard_of_isFinite_of_etale_of_isSepClosed
      (K := ((X.singularLocus K).subscheme.residueField s)) pt,
    Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq pt,
    Scheme.fromSpecResidueField_apply, X.finrank_branchSchemeToSingularLocus hnodal s]

/-- Over a separably closed field `K`, the branches of `X` through `s` biject with `Fin 2`. -/
theorem nonempty_equiv_fin_two_preimage_branchSchemeToSingularLocus
    (s : (letI := hnodal.syntomic; (X.singularLocus K).subscheme)) :
    letI := hnodal.syntomic
    Nonempty (Fin 2 ≃ (X.branchSchemeToSingularLocus K ⁻¹' {s})) := by
  have := hnodal.syntomic; have := X.isFinite_branchSchemeToSingularLocus hnodal
  have : Finite (X.branchSchemeToSingularLocus K ⁻¹' {s}) :=
    (X.branchSchemeToSingularLocus K).finite_preimage_singleton s
  exact ⟨(Finite.equivFinOfCardEq (X.natCard_preimage_branchSchemeToSingularLocus hnodal s)).symm⟩

/-- Over a separably closed field `K`, every singular point of `X` has two preimages in `Bl X`. -/
theorem ncard_preimage_blowupToBase_of_mem_support_singularLocus {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus K).support) :
    letI := hnodal.syntomic; ((X.singularLocus K).blowupToBase ⁻¹' {x}).ncard = 2 := by
  have := hnodal.syntomic
  obtain ⟨s, rfl⟩ := (Scheme.IdealSheafData.range_subschemeι (X.singularLocus K)).ge hx
  rw [← X.image_branchSchemeToBlowup_preimage_singleton s,
    Set.ncard_image_of_injective _ (X.branchSchemeToBlowup K).isEmbedding.injective,
    ← Nat.card_coe_set_eq, X.natCard_preimage_branchSchemeToSingularLocus hnodal s]

end NodalBranches

/-! ### The dual graph of a proper connected nodal curve over a separably closed field -/

section DualGraph

variable {K : Type u} [Field K] [IsSepClosed K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
  [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X]

omit [IsSepClosed K] [ConnectedSpace X] in
/-- Every proper nodal curve over a field has finitely many irreducible components in `Bl X`. -/
theorem finite_irreducibleComponents_blowup
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic; Finite (irreducibleComponents (X.singularLocus K).blowup) := by
  have := hnodal.syntomic; have := X.isFinite_blowupToBase_singularLocus hnodal
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K))
  have : CompactSpace (X.singularLocus K).blowup :=
    QuasiCompact.compactSpace_of_compactSpace (X.singularLocus K).blowupToBase
  have : IsLocallyNoetherian (X.singularLocus K).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian ((X.singularLocus K).blowupToBase ≫ (X ↘ Spec (.of K)))
  have : IsNoetherian (X.singularLocus K).blowup := {}
  exact NoetherianSpace.finite_irreducibleComponents

omit [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X] in
/-- Chosen bijection between `Fin 2` and the two branches over a node `e`. -/
def branchEquivOfNode (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (e : (letI := hnodal.syntomic; (X.singularLocus K).subscheme)) :
    letI := hnodal.syntomic; Fin 2 ≃ (X.branchSchemeToSingularLocus K ⁻¹' {e}) :=
  Classical.choice (X.nonempty_equiv_fin_two_preimage_branchSchemeToSingularLocus hnodal e)

omit [IsProper (X ↘ Spec (.of K))] in
/-- Any two irreducible components of `Bl X` for a connected nodal curve `X` are joined by a chain
of nodes. -/
theorem reflTransGen_markedDualGraph_adj
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v₀ w₀ : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
    let Bl := (X.singularLocus K).blowup
    let ep (e : (X.singularLocus K).subscheme) (i : Fin 2) : irreducibleComponents Bl :=
      Bl.componentOf (X.branchSchemeToBlowup K (X.branchEquivOfNode hnodal e i).1)
    Relation.ReflTransGen
      (fun v w ↦ ∃ e, (ep e 0 = v ∧ ep e 1 = w) ∨ (ep e 0 = w ∧ ep e 1 = v)) v₀ w₀ := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  have := X.isFinite_blowupToBase_singularLocus hnodal
  have := X.surjective_blowupToBase_singularLocus hnodal
  let Bl := (X.singularLocus K).blowup; let ν := (X.singularLocus K).blowupToBase
  let ep (e : (X.singularLocus K).subscheme) (i : Fin 2) : irreducibleComponents Bl :=
    Bl.componentOf (X.branchSchemeToBlowup K (X.branchEquivOfNode hnodal e i).1)
  let R (v w : irreducibleComponents Bl) : Prop :=
    ∃ e, (ep e 0 = v ∧ ep e 1 = w) ∨ (ep e 0 = w ∧ ep e 1 = v)
  let S : Set (irreducibleComponents Bl) := {w | Relation.ReflTransGen R v₀ w}; by_contra hw₀
  have hopen (T : Set (irreducibleComponents Bl)) : IsOpen {y : Bl | Bl.componentOf y ∈ T} := by
    have heq : {y : Bl | Bl.componentOf y ∈ T} = ⋃ w ∈ T, (w : Set Bl) := Set.ext fun y ↦ by
      simp only [mem_iUnion, exists_prop]; change Bl.componentOf y ∈ T ↔ _
      exact ⟨fun h ↦ ⟨Bl.componentOf y, h, Bl.mem_componentOf_self y⟩,
        fun ⟨w, hw, hy⟩ ↦ (Bl.componentOf_eq_iff.mpr hy).symm ▸ hw⟩
    exact heq ▸ isOpen_biUnion fun w _ ↦ (isClopen_of_mem_irreducibleComponents w.2).isOpen
  let U₁ : Set Bl := {y | Bl.componentOf y ∈ S}
  have huniv : ν '' U₁ ∪ ν '' U₁ᶜ = Set.univ := by
    rw [← image_union, union_compl_self, image_univ, ν.surjective.range_eq]
  obtain ⟨y₀, hy₀⟩ := v₀.2.1.nonempty; obtain ⟨z₀, hz₀⟩ := w₀.2.1.nonempty
  have hy₀S : y₀ ∈ U₁ := by change _ ∈ S; rw [Bl.componentOf_eq_iff.mpr hy₀]; exact .refl
  have hz₀S : z₀ ∈ U₁ᶜ := fun hz ↦ hw₀ (Bl.componentOf_eq_iff.mpr hz₀ ▸ hz)
  have hnotdisj : ¬ Disjoint (ν '' U₁) (ν '' U₁ᶜ) := fun hdisj ↦ by
    have hcompl : ν '' U₁ = (ν '' U₁ᶜ)ᶜ := Set.ext fun x ↦
      ⟨fun hx₁ hx₂ ↦ disjoint_left.mp hdisj hx₁ hx₂,
        fun hx₂ ↦ (huniv ▸ trivial : x ∈ ν '' U₁ ∪ ν '' U₁ᶜ).resolve_right hx₂⟩
    have heq : ν '' U₁ = Set.univ := IsClopen.eq_univ
      ⟨ν.isClosedMap U₁ (isOpen_compl_iff.mp (hopen Sᶜ)),
        hcompl ▸ (ν.isClosedMap U₁ᶜ (hopen S).isClosed_compl).isOpen_compl⟩ ⟨ν y₀, y₀, hy₀S, rfl⟩
    exact disjoint_left.mp hdisj (heq ▸ trivial) ⟨z₀, hz₀S, rfl⟩
  obtain ⟨_, ⟨y₁, hy₁S, rfl⟩, ⟨y₂, hy₂S, hy₂eq⟩⟩ := Set.not_disjoint_iff.mp hnotdisj
  have hne_comp : Bl.componentOf y₁ ≠ Bl.componentOf y₂ :=
    fun h ↦ hy₂S (by change _ ∈ S at hy₁S ⊢; rwa [← h])
  have hxSing : ν y₁ ∈ ((X.singularLocus K).support : Set X) := by
    rw [X.support_singularLocus_eq_compl_smoothLocus, mem_compl_iff]
    exact fun hxU ↦ hne_comp (congrArg Bl.componentOf
      (eq_of_blowupToBase_eq_of_mem_smoothLocus hnodal hy₂eq.symm hxU))
  obtain ⟨e, he⟩ := (Scheme.IdealSheafData.range_subschemeι (X.singularLocus K)).ge hxSing
  obtain ⟨b₁, hb₁s, hb₁y⟩ := exists_preimage_of_isPullback (X.isPullback_branchScheme K) e y₁ he
  obtain ⟨b₂, hb₂s, hb₂y⟩ :=
    exists_preimage_of_isPullback (X.isPullback_branchScheme K) e y₂ (he.trans hy₂eq.symm)
  let i₁ := (X.branchEquivOfNode hnodal e).symm ⟨b₁, hb₁s⟩
  let i₂ := (X.branchEquivOfNode hnodal e).symm ⟨b₂, hb₂s⟩
  have hi₁ : ep e i₁ = Bl.componentOf y₁ := by simp [ep, i₁, hb₁y]
  have hi₂ : ep e i₂ = Bl.componentOf y₂ := by simp [ep, i₂, hb₂y]
  have h01 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  rcases h01 i₁ i₂ (fun h ↦ hne_comp (hi₁ ▸ hi₂ ▸ congrArg (ep e) h)) with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · exact hy₂S (hy₁S.tail ⟨e, .inl ⟨h0 ▸ hi₁, h1 ▸ hi₂⟩⟩)
  · exact hy₂S (hy₁S.tail ⟨e, .inr ⟨h0 ▸ hi₂, h1 ▸ hi₁⟩⟩)

variable (K) in
/-- The marked dual graph of a proper connected nodal curve over a separably closed field. -/
abbrev markedDualGraph (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    {ι : Type v} (p : ι → (letI := hnodal.syntomic; (X ↘ Spec (.of K)).smoothLocus)) :
    DualGraph.{u, v} ι :=
  letI := hnodal.syntomic; haveI := X.isRegular_blowup_singularLocus hnodal
  haveI := X.surjective_blowupToBase_singularLocus hnodal
  haveI := X.isFinite_singularLocus_subschemeι_comp hnodal
  haveI := X.etale_singularLocus_subschemeι_comp hnodal
  let Bl := (X.singularLocus K).blowup; let Sing := (X.singularLocus K).subscheme
  haveI : Finite (irreducibleComponents Bl) := X.finite_irreducibleComponents_blowup hnodal
  haveI : Finite Sing :=
    finite_of_isFinite_of_etale ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K)))
  haveI : Nonempty Bl := (X.singularLocus K).blowupToBase.surjective.nonempty
  haveI : Nonempty (irreducibleComponents Bl) := ⟨Bl.componentOf (Classical.arbitrary Bl)⟩
  letI := Classical.decEq (irreducibleComponents Bl); letI := Classical.decEq Sing
  letI := Fintype.ofFinite (irreducibleComponents Bl); letI := Fintype.ofFinite Sing
  { Vertex := irreducibleComponents Bl
    Edge := Sing
    endpoint e i := Bl.componentOf (X.branchSchemeToBlowup K (X.branchEquivOfNode hnodal e i).1)
    genus v := X.componentGenus K hnodal v
    marking i := Bl.componentOf (Classical.choose
      (existsUnique_blowupToBase_eq_of_mem_smoothLocus hnodal (p i).2).exists)
    connected := X.reflTransGen_markedDualGraph_adj hnodal }

variable (K) in
/-- The unmarked dual graph of a proper connected nodal curve over a separably closed field. -/
abbrev dualGraph (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    DualGraph.{u, 0} Empty :=
  X.markedDualGraph K hnodal Empty.elim

section MarkedDualGraphProps

variable (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
  {ι : Type v} (p : ι → (letI := hnodal.syntomic; (X ↘ Spec (.of K)).smoothLocus))

@[simp]
theorem markedDualGraph_vertex :
    letI := hnodal.syntomic
    (X.markedDualGraph K hnodal p).Vertex =
      irreducibleComponents (X.singularLocus K).blowup := (rfl)

@[simp]
theorem markedDualGraph_edge :
    letI := hnodal.syntomic
    (X.markedDualGraph K hnodal p).Edge = (X.singularLocus K).subscheme := (rfl)

/-- Reindexing the smooth marked points reindexes the marked dual graph. -/
@[simp]
theorem markedDualGraph_comp {κ : Type*} (e : κ → ι) :
    X.markedDualGraph K hnodal (p ∘ e) = (X.markedDualGraph K hnodal p).reindex e := (rfl)

/-- Choice-free characterization of `marking` via membership in the component of `X`. -/
theorem markedDualGraph_marking_eq_iff (i : ι)
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    (X.markedDualGraph K hnodal p).marking i = v ↔
      (p i).1 ∈ ((X.blowupComponentEquiv K hnodal v : irreducibleComponents X) : Set X) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  let y := Classical.choose (existsUnique_blowupToBase_eq_of_mem_smoothLocus hnodal (p i).2).exists
  have hy : (X.singularLocus K).blowupToBase y = (p i).1 := Classical.choose_spec
    (existsUnique_blowupToBase_eq_of_mem_smoothLocus hnodal (p i).2).exists
  change (X.singularLocus K).blowup.componentOf y = v ↔ _
  rw [(X.singularLocus K).blowup.componentOf_eq_iff, ← hy,
    blowupToBase_mem_coe_blowupComponentEquiv_iff_of_mem_smoothLocus hnodal (hy.symm ▸ (p i).2)]

/-- The number of vertices of `markedDualGraph` equals `(irreducibleComponents X).ncard`. -/
theorem natCard_vertex_markedDualGraph :
    Nat.card (X.markedDualGraph K hnodal p).Vertex = (irreducibleComponents X).ncard := by
  have := hnodal.syntomic
  rw [markedDualGraph_vertex, Nat.card_congr (X.blowupComponentEquiv K hnodal), Nat.card_coe_set_eq]

/-- The number of edges of `markedDualGraph` equals the number of singular points of `X`. -/
theorem natCard_edge_markedDualGraph :
    letI := hnodal.syntomic
    Nat.card (X.markedDualGraph K hnodal p).Edge =
      ((X.singularLocus K).support : Set X).ncard := by
  have := hnodal.syntomic
  rw [markedDualGraph_edge, ← Scheme.IdealSheafData.range_subschemeι,
    Set.ncard_range_of_injective (X.singularLocus K).subschemeι.isEmbedding.injective]

section VertexProps

variable (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup)
  (e : letI := hnodal.syntomic; (X.singularLocus K).subscheme)

theorem markedDualGraph_genus :
    (X.markedDualGraph K hnodal p).genus v = X.componentGenus K hnodal v := (rfl)

/-- `v` is an endpoint of `e` iff `v` contains a point of `Bl X` lying over `e`. -/
theorem mem_ends_markedDualGraph_iff :
    letI := hnodal.syntomic
    v ∈ (X.markedDualGraph K hnodal p).ends e ↔
      ∃ y ∈ (v : Set (X.singularLocus K).blowup),
        (X.singularLocus K).blowupToBase y = (X.singularLocus K).subschemeι e := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  rw [DualGraph.mem_ends_iff]
  change (∃ i : Fin 2, (X.singularLocus K).blowup.componentOf
      (X.branchSchemeToBlowup K (X.branchEquivOfNode hnodal e i).1) = v) ↔ _
  simp only [(X.singularLocus K).blowup.componentOf_eq_iff]
  refine ⟨fun ⟨i, hi⟩ ↦ ⟨_, hi, ?_⟩, fun ⟨y, hyv, hy⟩ ↦ ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← X.branchSchemeToSingularLocus_subschemeι K,
      Scheme.Hom.comp_apply, mem_singleton_iff.mp (X.branchEquivOfNode hnodal e i).2]
  · obtain ⟨b, hbs, rfl⟩ := exists_preimage_of_isPullback (X.isPullback_branchScheme K) e y hy.symm
    exact ⟨(X.branchEquivOfNode hnodal e).symm ⟨b, hbs⟩, by simp [hyv]⟩

/-- `v` is an endpoint of `e` iff the node `e` lies on the corresponding component of `X`. -/
theorem mem_ends_markedDualGraph_iff_subschemeι_mem :
    letI := hnodal.syntomic
    v ∈ (X.markedDualGraph K hnodal p).ends e ↔
      (X.singularLocus K).subschemeι e ∈
        ((X.blowupComponentEquiv K hnodal v : irreducibleComponents X) : Set X) := by
  have := hnodal.syntomic
  rw [X.mem_ends_markedDualGraph_iff hnodal p v e, X.coe_blowupComponentEquiv hnodal v, mem_image]

/-- A node `e` is a loop at `v` iff the entire blowup fiber over `e` lies in `v`. -/
theorem ends_markedDualGraph_eq_self_iff :
    letI := hnodal.syntomic
    (X.markedDualGraph K hnodal p).ends e = s(v, v) ↔
      (X.singularLocus K).blowupToBase ⁻¹' {(X.singularLocus K).subschemeι e} ⊆
        (v : Set (X.singularLocus K).blowup) := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  let G := X.markedDualGraph K hnodal p
  rw [G.ends_def, Sym2.eq_iff, or_self]
  change (G.endpoint e 0 = v ∧ G.endpoint e 1 = v) ↔ _
  rw [← Fin.forall_fin_two (p := fun i ↦ G.endpoint e i = v)]
  change (∀ i : Fin 2, (X.singularLocus K).blowup.componentOf
      (X.branchSchemeToBlowup K (X.branchEquivOfNode hnodal e i).1) = v) ↔ _
  simp only [(X.singularLocus K).blowup.componentOf_eq_iff]
  rw [← X.image_branchSchemeToBlowup_preimage_singleton e, image_subset_iff]
  exact ⟨fun h b hb ↦ by simpa using h ((X.branchEquivOfNode hnodal e).symm ⟨b, hb⟩),
    fun h i ↦ h (X.branchEquivOfNode hnodal e i).2⟩

/-- The valence of `v` in `markedDualGraph` equals the number of points of `v` over `Sing(X/K)`. -/
theorem valence_markedDualGraph :
    letI := hnodal.syntomic
    (X.markedDualGraph K hnodal p).valence v =
      ((v : Set (X.singularLocus K).blowup) ∩
        (X.singularLocus K).blowupToBase ⁻¹' (X.singularLocus K).support).ncard := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  let Bl := (X.singularLocus K).blowup; let G := X.markedDualGraph K hnodal p
  let := G.edgeFintype; let := G.vertexDecidableEq
  let φ : G.Edge × Fin 2 → Bl := fun h ↦
    X.branchSchemeToBlowup K (X.branchEquivOfNode hnodal h.1 h.2).1
  have hφ_inj : Function.Injective φ := fun ⟨e₁, i₁⟩ ⟨e₂, i₂⟩ heq ↦ by
    have hb := (X.branchSchemeToBlowup K).isEmbedding.injective heq
    have he : e₁ = e₂ := (mem_singleton_iff.mp (X.branchEquivOfNode hnodal e₁ i₁).2).symm.trans
      ((congrArg (X.branchSchemeToSingularLocus K) hb).trans
        (mem_singleton_iff.mp (X.branchEquivOfNode hnodal e₂ i₂).2))
    subst he; exact Prod.ext rfl ((X.branchEquivOfNode hnodal e₁).injective (Subtype.ext hb))
  let S : Finset (G.Edge × Fin 2) := Finset.univ.filter fun h ↦ G.endpoint h.1 h.2 = v
  have himg : φ '' (S : Set (G.Edge × Fin 2)) =
      (v : Set Bl) ∩ (X.singularLocus K).blowupToBase ⁻¹' (X.singularLocus K).support := by
    rw [← X.range_branchSchemeToBlowup]; ext y
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, mem_image,
      mem_inter_iff, mem_range]
    refine ⟨by rintro ⟨⟨e, i⟩, hv, rfl⟩; exact ⟨Bl.componentOf_eq_iff.mp hv, _, rfl⟩, ?_⟩
    rintro ⟨hyv, b, rfl⟩; let e' := X.branchSchemeToSingularLocus K b
    let i := (X.branchEquivOfNode hnodal e').symm ⟨b, rfl⟩
    exact ⟨(e', i), Bl.componentOf_eq_iff.mpr (by simpa [φ, i] using hyv), by simp [φ, i]⟩
  rw [G.valence_def, ← himg, Set.ncard_image_of_injective _ hφ_inj, Set.ncard_coe_finset]

end VertexProps

end MarkedDualGraphProps

/-! ### Smooth curves -/

section Smooth

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of K))]
  {ι : Type v} (p : ι → (X ↘ Spec (.of K)).smoothLocus)

/-- The dual graph of a smooth proper connected curve has no edges. -/
theorem isEmpty_edge_markedDualGraph_of_smooth :
    IsEmpty (X.markedDualGraph K (.of_smooth (X ↘ Spec (.of K))) p).Edge := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of K))
  have := (AtWorstNodalOfRelativeDimensionOne.of_smooth (X ↘ Spec (.of K))).syntomic
  refine ⟨fun e ↦ ?_⟩
  have hmem : (X.singularLocus K).subschemeι e ∈ ((X.singularLocus K).support : Set X) :=
    (Scheme.IdealSheafData.range_subschemeι _).subset ⟨e, rfl⟩
  rw [X.support_singularLocus_eq_compl_smoothLocus, Scheme.Hom.smoothLocus_eq_top] at hmem
  exact hmem trivial

/-- The dual graph of a smooth proper connected curve has a unique vertex. -/
theorem subsingleton_vertex_markedDualGraph_of_smooth :
    Subsingleton (X.markedDualGraph K (.of_smooth (X ↘ Spec (.of K))) p).Vertex := by
  have := X.isEmpty_edge_markedDualGraph_of_smooth p
  let G := X.markedDualGraph K (.of_smooth (X ↘ Spec (.of K))) p
  exact ⟨fun v w ↦ (G.eq_of_forall_endpoint_zero_eq_iff (v := v) fun e ↦ isEmptyElim e) w |>.symm⟩

/-- The dual graph of a smooth proper connected curve has first Betti number zero. -/
@[simp]
theorem firstBetti_markedDualGraph_of_smooth :
    (X.markedDualGraph K (.of_smooth (X ↘ Spec (.of K))) p).firstBetti = 0 := by
  have := X.isEmpty_edge_markedDualGraph_of_smooth p
  have := X.subsingleton_vertex_markedDualGraph_of_smooth p
  let G := X.markedDualGraph K (.of_smooth (X ↘ Spec (.of K))) p
  let := G.vertexFintype; let := G.edgeFintype; let := G.vertexNonempty
  have hadd := G.firstBetti_add_card_vertex
  rw [Fintype.card_eq_zero (α := G.Edge), Fintype.card_eq_one_iff.mpr
    ⟨Classical.arbitrary G.Vertex, fun w ↦ Subsingleton.elim w _⟩] at hadd
  change G.firstBetti = 0; omega

private theorem isIso_of_isOpenImmersion_of_surjective {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] [Surjective f] : IsIso f := by
  rw [isIso_iff_isOpenImmersion_and_epi_base, TopCat.epi_iff_surjective]
  exact ⟨inferInstance, f.surjective⟩

/-- For a smooth proper connected curve, the combinatorial arithmetic genus equals `X.genus K`. -/
@[simp]
theorem arithmeticGenus_markedDualGraph_of_smooth :
    haveI : (InvertibleSheaf.trivial X).obj.IsFinitePresentation :=
      ((InvertibleSheaf.toFinitelyPresented X).obj (InvertibleSheaf.trivial X)).property
    haveI := Scheme.Modules.finiteDimensional_cohomology_of_smooth K
      (InvertibleSheaf.trivial X).obj 1
    (X.markedDualGraph K (.of_smooth (X ↘ Spec (.of K))) p).arithmeticGenus = X.genus K := by
  let hnodal := AtWorstNodalOfRelativeDimensionOne.of_smooth (X ↘ Spec (.of K))
  have := hnodal.syntomic; have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of K))
  have : IsIso ((X.singularLocus K).blowupToBase ∣_ (X ↘ Spec (.of K)).smoothLocus) :=
    X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  have : IsIso (X.singularLocus K).blowupToBase := by
    let U := (X ↘ Spec (.of K)).smoothLocus; let W := (X.singularLocus K).blowupToBase ⁻¹ᵁ U
    have htop : U = ⊤ := Scheme.Hom.smoothLocus_eq_top _
    have : Surjective W.ι := ⟨fun y ↦ ⟨⟨y, by change _ ∈ U; rw [htop]; trivial⟩, rfl⟩⟩
    have : IsIso W.ι := isIso_of_isOpenImmersion_of_surjective _
    have : IsIso (W.ι ≫ (X.singularLocus K).blowupToBase) := by
      have : Surjective U.ι := ⟨fun x ↦ ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩⟩
      have : IsIso U.ι := isIso_of_isOpenImmersion_of_surjective _
      rw [← morphismRestrict_ι]; infer_instance
    exact IsIso.of_isIso_comp_left W.ι (X.singularLocus K).blowupToBase
  have := X.isRegular_blowup_singularLocus hnodal
  have := X.isEmpty_edge_markedDualGraph_of_smooth p
  have := X.subsingleton_vertex_markedDualGraph_of_smooth p
  let G := X.markedDualGraph K hnodal p; let := G.vertexNonempty
  let v : G.Vertex := Classical.arbitrary G.Vertex
  have hv_univ : (v : Set (X.singularLocus K).blowup) = Set.univ := eq_univ_iff_forall.mpr fun _ ↦
    (X.singularLocus K).blowup.componentOf_eq_iff.mp (Subsingleton.elim _ _)
  have : Surjective (X.normalizedComponentι K hnodal v) :=
    ⟨Set.range_eq_univ.mp ((X.range_normalizedComponentι hnodal v).trans hv_univ)⟩
  have : IsIso (X.normalizedComponentι K hnodal v) := isIso_of_isOpenImmersion_of_surjective _
  have : IsIso (X.normalizedComponentToCurve K hnodal v) := by
    rw [X.normalizedComponentToCurve_def hnodal v]; infer_instance
  have : (InvertibleSheaf.trivial X).obj.IsFinitePresentation :=
    ((InvertibleSheaf.toFinitelyPresented X).obj (InvertibleSheaf.trivial X)).property
  have := Scheme.Modules.finiteDimensional_cohomology_of_smooth K (InvertibleSheaf.trivial X).obj 1
  have := X.finiteDimensional_cohomology_invertibleSheaf_normalizedComponent hnodal v
    (InvertibleSheaf.trivial _) 1
  have Hpb : IsPullback (X.normalizedComponentToCurve K hnodal v)
      (X.normalizedComponent K hnodal v ↘ Spec (.of K))
      (X ↘ Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ by rw [← Spec.map_id]; rfl]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← normalizedComponent_over_hom]⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of K))
  have hval : G.valence v = 0 := G.valence_eq_zero_iff.mpr fun e ↦ isEmptyElim e
  have htwo := G.two_mul_arithmeticGenus_of_forall_endpoint_zero_eq_iff (v := v)
    fun e ↦ isEmptyElim e
  have hgen : G.arithmeticGenus = X.componentGenus K hnodal v := by change _ = G.genus v; omega
  rw [hgen, componentGenus_def, Scheme.genus_def, Scheme.genus_def]
  exact finrank_cohomology_trivial_eq_of_isPullback Hpb 1

end Smooth

/-! ### Geometric rational tails and rational bridges -/

omit [ConnectedSpace X] in
variable (K) in
/-- A component `v` is a geometric rational tail if it is smooth of genus `0` and meets the union
of the remaining components of `X` in a single point. -/
def IsRationalTail (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) : Prop :=
  letI := hnodal.syntomic; let E := X.blowupComponentEquiv K hnodal v
  X.componentGenus K hnodal v = 0 ∧
    Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup) ∧
    ((E : Set X) ∩ ⋃ E' ∈ irreducibleComponents X \ {(E : Set X)}, E').ncard = 1

omit [ConnectedSpace X] in
variable (K) in
/-- A component `v` is a geometric rational bridge if it is smooth of genus `0` and meets the union
of the remaining components of `X` in two points. -/
def IsRationalBridge (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) : Prop :=
  letI := hnodal.syntomic; let E := X.blowupComponentEquiv K hnodal v
  X.componentGenus K hnodal v = 0 ∧
    Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup) ∧
    ((E : Set X) ∩ ⋃ E' ∈ irreducibleComponents X \ {(E : Set X)}, E').ncard = 2

section RationalTailsBridges

variable (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
  {ι : Type v} (p : ι → (letI := hnodal.syntomic; (X ↘ Spec (.of K)).smoothLocus))

/-- `blowupToBase` is injective on `v` iff no edge of `markedDualGraph` is a loop at `v`. -/
theorem injOn_blowupToBase_iff_forall_ends_ne_self
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup) ↔
      ∀ e, (X.markedDualGraph K hnodal p).ends e ≠ s(v, v) := by
  have := hnodal.syntomic; let ν := (X.singularLocus K).blowupToBase
  simp only [ne_eq, X.ends_markedDualGraph_eq_self_iff hnodal p v]
  refine ⟨fun hinj e hsub ↦ ?_, fun hnoloop y₁ hy₁ y₂ hy₂ heq ↦ ?_⟩
  · obtain ⟨y₁, y₂, hne, hpair⟩ := Set.ncard_eq_two.mp
      (X.ncard_preimage_blowupToBase_of_mem_support_singularLocus hnodal
        ((Scheme.IdealSheafData.range_subschemeι (X.singularLocus K)).subset ⟨e, rfl⟩))
    have hy₁ : y₁ ∈ ν ⁻¹' {(X.singularLocus K).subschemeι e} := hpair ▸ mem_insert _ _
    have hy₂ : y₂ ∈ ν ⁻¹' {(X.singularLocus K).subschemeι e} :=
      hpair ▸ mem_insert_of_mem _ (mem_singleton _)
    exact hne (hinj (hsub hy₁) (hsub hy₂)
      ((mem_singleton_iff.mp hy₁).trans (mem_singleton_iff.mp hy₂).symm))
  · by_cases hU : ν y₁ ∈ (X ↘ Spec (.of K)).smoothLocus
    · exact eq_of_blowupToBase_eq_of_mem_smoothLocus hnodal heq hU
    · have hSing : ν y₁ ∈ ((X.singularLocus K).support : Set X) := by
        rwa [X.support_singularLocus_eq_compl_smoothLocus, mem_compl_iff]
      obtain ⟨e, he⟩ := (Scheme.IdealSheafData.range_subschemeι (X.singularLocus K)).ge hSing
      by_contra hne
      have hcard := X.ncard_preimage_blowupToBase_of_mem_support_singularLocus hnodal
        ((Scheme.IdealSheafData.range_subschemeι (X.singularLocus K)).subset ⟨e, rfl⟩)
      have hpair : ({y₁, y₂} : Set _) = ν ⁻¹' {(X.singularLocus K).subschemeι e} :=
        Set.eq_of_subset_of_ncard_le (pair_subset_iff.mpr ⟨he.symm, heq.symm.trans he.symm⟩)
          (by rw [hcard, Set.ncard_pair hne]) (Set.finite_of_ncard_ne_zero (by rw [hcard]; decide))
      exact hnoloop e (hpair ▸ pair_subset_iff.mpr ⟨hy₁, hy₂⟩)

omit [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X] in
/-- When `blowupToBase` is injective on `v`, it maps `v ∩ ν ⁻¹' Sing(X/K)` onto the intersection of
`ν '' v` with the union of the remaining irreducible components of `X`. -/
theorem image_blowupToBase_inter_preimage_singularLocus_of_injOn
    {v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup}
    (hinj : letI := hnodal.syntomic
      Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup)) :
    letI := hnodal.syntomic; let E := X.blowupComponentEquiv K hnodal v
    (X.singularLocus K).blowupToBase ''
        ((v : Set (X.singularLocus K).blowup) ∩
          (X.singularLocus K).blowupToBase ⁻¹' (X.singularLocus K).support) =
      (E : Set X) ∩ ⋃ E' ∈ irreducibleComponents X \ {(E : Set X)}, E' := by
  have := hnodal.syntomic; have := X.isRegular_blowup_singularLocus hnodal
  let Bl := (X.singularLocus K).blowup; let ν := (X.singularLocus K).blowupToBase
  let E := X.blowupComponentEquiv K hnodal v; ext x
  simp only [mem_image, mem_inter_iff, mem_preimage, mem_iUnion, mem_sdiff, mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨hyv, hxSing⟩, rfl⟩
    refine ⟨(X.coe_blowupComponentEquiv hnodal v).symm ▸ ⟨y, hyv, rfl⟩, ?_⟩
    have hcard : (ν ⁻¹' {ν y}).ncard = 2 :=
      X.ncard_preimage_blowupToBase_of_mem_support_singularLocus hnodal hxSing
    obtain ⟨z, hz, hzy⟩ := Set.exists_ne_of_one_lt_ncard (s := ν ⁻¹' {ν y}) (by omega) y
    have hzv : z ∉ (v : Set Bl) := fun hzv ↦ hzy (hinj hzv hyv (mem_singleton_iff.mp hz))
    let w := Bl.componentOf z; have hwv : w ≠ v := fun hw ↦ hzv (hw ▸ Bl.mem_componentOf_self z)
    exact ⟨(X.blowupComponentEquiv K hnodal w : Set X), ⟨(X.blowupComponentEquiv K hnodal w).2,
        fun hEq ↦ hwv ((X.blowupComponentEquiv K hnodal).injective (Subtype.ext hEq))⟩,
      (X.coe_blowupComponentEquiv hnodal w).symm ▸
        ⟨z, Bl.mem_componentOf_self z, mem_singleton_iff.mp hz⟩⟩
  · rintro ⟨hxE, E', ⟨hE', hE'ne⟩, hxE'⟩
    obtain ⟨y, hyv, rfl⟩ : x ∈ ν '' (v : Set Bl) := X.coe_blowupComponentEquiv hnodal v ▸ hxE
    refine ⟨y, ⟨hyv, ?_⟩, rfl⟩; change ν y ∈ ((X.singularLocus K).support : Set X)
    rw [X.support_singularLocus_eq_compl_smoothLocus, mem_compl_iff]
    exact fun hyU ↦ hE'ne (congrArg Subtype.val <|
      (existsUnique_mem_irreducibleComponents_of_mem_smoothLocus hnodal hyU).unique
        (y₁ := ⟨E', hE'⟩) (y₂ := E) hxE' hxE)

/-- For `v` without self-nodes, `valence v` equals the number of intersection points of `ν '' v`
with the union of the remaining irreducible components of `X`. -/
theorem valence_markedDualGraph_eq_ncard_inter_other_components_of_injOn
    {v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup}
    (hinj : letI := hnodal.syntomic
      Set.InjOn (X.singularLocus K).blowupToBase (v : Set (X.singularLocus K).blowup)) :
    letI := hnodal.syntomic; let E := X.blowupComponentEquiv K hnodal v
    (X.markedDualGraph K hnodal p).valence v =
      ((E : Set X) ∩ ⋃ E' ∈ irreducibleComponents X \ {(E : Set X)}, E').ncard := by
  have := hnodal.syntomic; dsimp only
  rw [X.valence_markedDualGraph hnodal p v,
    ← X.image_blowupToBase_inter_preimage_singularLocus_of_injOn hnodal hinj]
  exact (hinj.mono inter_subset_left).ncard_image.symm

/-- Equivalence between combinatorial and geometric rational tails. -/
theorem markedDualGraph_isRationalTail_iff
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    (X.markedDualGraph K hnodal p).IsRationalTail v ↔ X.IsRationalTail K hnodal v := by
  have := hnodal.syntomic; let G := X.markedDualGraph K hnodal p
  let := G.edgeFintype; let := G.edgeDecidableEq; let := G.vertexDecidableEq
  rw [G.isRationalTail_iff, IsRationalTail, markedDualGraph_genus]
  refine and_congr_right fun _ ↦ ⟨fun hval ↦ ?_, fun ⟨hinj, hcard⟩ ↦
    (X.valence_markedDualGraph_eq_ncard_inter_other_components_of_injOn hnodal p hinj).trans hcard⟩
  have hinj : Set.InjOn (X.singularLocus K).blowupToBase
      (v : Set (X.singularLocus K).blowup) := by
    rw [X.injOn_blowupToBase_iff_forall_ends_ne_self hnodal p v]; intro e he
    rw [G.ends_def, Sym2.eq_iff, or_self] at he
    have hsub : ({(e, 0), (e, 1)} : Finset (G.Edge × Fin 2)) ⊆
        Finset.univ.filter fun h ↦ G.endpoint h.1 h.2 = v := by
      rintro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
      · simp [he.1]
      · simp [Finset.mem_singleton.mp hx, he.2]
    have hle : 2 ≤ G.valence v := by rw [G.valence_def]; simpa using Finset.card_le_card hsub
    omega
  exact ⟨hinj,
    (X.valence_markedDualGraph_eq_ncard_inter_other_components_of_injOn hnodal p hinj).symm.trans
      hval⟩

/-- Equivalence between combinatorial and geometric rational bridges. -/
theorem markedDualGraph_isRationalBridge_iff
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    (X.markedDualGraph K hnodal p).IsRationalBridge v ↔ X.IsRationalBridge K hnodal v := by
  have := hnodal.syntomic; let G := X.markedDualGraph K hnodal p
  rw [G.isRationalBridge_iff, G.forall_endpoint_one_ne_iff,
    ← X.injOn_blowupToBase_iff_forall_ends_ne_self hnodal p v, IsRationalBridge,
    markedDualGraph_genus]
  exact and_congr_right fun _ ↦ ⟨fun ⟨hval, hinj⟩ ↦ ⟨hinj,
      (X.valence_markedDualGraph_eq_ncard_inter_other_components_of_injOn hnodal p hinj).symm.trans
        hval⟩,
    fun ⟨hinj, hcard⟩ ↦
      ⟨(X.valence_markedDualGraph_eq_ncard_inter_other_components_of_injOn hnodal p hinj).trans
        hcard, hinj⟩⟩

/-- Geometric semistability criterion for an unpointed curve of arithmetic genus `≥ 1`. -/
theorem dualGraph_isSemistable_iff (hg : 1 ≤ (X.dualGraph K hnodal).arithmeticGenus) :
    (X.dualGraph K hnodal).IsSemistable ↔ ∀ v, ¬ X.IsRationalTail K hnodal v := by
  rw [dualGraph,
    (X.markedDualGraph K hnodal Empty.elim).isSemistable_iff_forall_not_isRationalTail hg]
  simp only [X.markedDualGraph_isRationalTail_iff hnodal Empty.elim]

/-- Geometric stability criterion for an unpointed curve of arithmetic genus `≥ 2`. -/
theorem dualGraph_isStable_iff (hg : 2 ≤ (X.dualGraph K hnodal).arithmeticGenus) :
    (X.dualGraph K hnodal).IsStable ↔
      ∀ v, ¬ X.IsRationalTail K hnodal v ∧ ¬ X.IsRationalBridge K hnodal v := by
  rw [dualGraph, (X.markedDualGraph K hnodal
    Empty.elim).isStable_iff_forall_not_isRationalTail_and_not_isRationalBridge hg]
  simp only [X.markedDualGraph_isRationalTail_iff hnodal Empty.elim,
    X.markedDualGraph_isRationalBridge_iff hnodal Empty.elim]

end RationalTailsBridges

end DualGraph

/-! ### Base change of branch schemes and invariance of dual graphs -/

section BranchBaseChange

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  {X X' : Scheme.{u}} [X.Over (Spec (.of R))] [X'.Over (Spec (.of R'))] {g : X' ⟶ X}
  [Flat (X ↘ Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [PureRelativeDimension 1 (X ↘ Spec (.of R))]
  [Flat (X' ↘ Spec (.of R'))] [LocallyOfFinitePresentation (X' ↘ Spec (.of R'))]
  [PureRelativeDimension 1 (X' ↘ Spec (.of R'))]
  (H : IsPullback g (X' ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

/-- Induced morphism `X'.branchScheme R' ⟶ X.branchScheme R` under base change of `X`. -/
def branchSchemeBaseChangeMap : X'.branchScheme R' ⟶ X.branchScheme R :=
  (X.isPullback_branchScheme R).lift
    (X'.branchSchemeToSingularLocus R' ≫
      (X'.singularLocus R').subschemeMap (X.singularLocus R) g
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (Scheme.singularLocus_eq_comap_of_isPullback H).ge))
    (X'.branchSchemeToBlowup R' ≫ singularLocusBlowupMap H)
    (by
      rw [Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
        ← Category.assoc, X'.branchSchemeToSingularLocus_subschemeι R',
        Category.assoc, ← singularLocusBlowupMap_blowupToBase H, Category.assoc])

@[reassoc (attr := simp)]
theorem branchSchemeBaseChangeMap_toSingularLocus :
    branchSchemeBaseChangeMap H ≫ X.branchSchemeToSingularLocus R =
      X'.branchSchemeToSingularLocus R' ≫
        (X'.singularLocus R').subschemeMap (X.singularLocus R) g
          (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
            (Scheme.singularLocus_eq_comap_of_isPullback H).ge) :=
  (X.isPullback_branchScheme R).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem branchSchemeBaseChangeMap_toBlowup :
    branchSchemeBaseChangeMap H ≫ X.branchSchemeToBlowup R =
      X'.branchSchemeToBlowup R' ≫ singularLocusBlowupMap H :=
  (X.isPullback_branchScheme R).lift_snd _ _ _

/-- Under flat base change, `branchSchemeBaseChangeMap H` is a pullback over singular subschemes. -/
theorem isPullback_branchSchemeBaseChangeMap [Module.Flat R R'] :
    IsPullback (branchSchemeBaseChangeMap H) (X'.branchSchemeToSingularLocus R')
      (X.branchSchemeToSingularLocus R)
      ((X'.singularLocus R').subschemeMap (X.singularLocus R) g
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (Scheme.singularLocus_eq_comap_of_isPullback H).ge)) := by
  refine IsPullback.of_right ?_ (branchSchemeBaseChangeMap_toSingularLocus H)
    (X.isPullback_branchScheme R).flip
  rw [branchSchemeBaseChangeMap_toBlowup H, Scheme.IdealSheafData.subschemeMap_subschemeι]
  exact (X'.isPullback_branchScheme R').flip.paste_horiz (isPullback_singularLocusBlowupMap H).flip

end BranchBaseChange

section DualGraphBaseChange

/-- Properness of scheme morphisms is preserved along arbitrary pullback squares. -/
theorem isProper_of_isPullback {P Y Z W : Scheme.{u}} {fst : P ⟶ Y} {snd : P ⟶ Z}
    {f : Y ⟶ W} {g : Z ⟶ W} (H : IsPullback fst snd f g) [IsProper f] : IsProper snd :=
  MorphismProperty.of_isPullback H ‹_›

/-- Over a separably closed field `K`, base change to any `K`-algebra with irreducible spectrum
preserves connectedness. -/
theorem connectedSpace_of_isPullback_of_isSepClosed {K M : Type u} [Field K] [IsSepClosed K]
    [CommRing M] [Algebra K M] [IrreducibleSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} [ConnectedSpace X] {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)}
    {g : X' ⟶ X} (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M)))) :
    ConnectedSpace X' := by
  have : GeometricallyConnected g := MorphismProperty.of_isPullback H.flip inferInstance
  have : UniversallyOpen g := MorphismProperty.of_isPullback H.flip inferInstance
  exact GeometricallyConnected.connectedSpace g g.isOpenMap

variable {K L : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L] [Algebra K L]
  {X X' : Scheme.{u}} [X.Over (Spec (.of K))] [X'.Over (Spec (.of L))]
  [IsProper (X ↘ Spec (.of K))] [ConnectedSpace X] {g : X' ⟶ X}

section PullbackIso

variable (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
  (H : IsPullback g (X' ↘ Spec (.of L)) (X ↘ Spec (.of K)) (Spec.algebraMap K L))

/-- Canonical isomorphism of marked dual graphs under extension of separably closed base fields. -/
def markedDualGraphBaseChangeIso
    {ι : Type v} (p : ι → (letI := hnodal.syntomic; (X ↘ Spec (.of K)).smoothLocus))
    (p' : ι → (letI := (MorphismProperty.of_isPullback H hnodal).syntomic
      (X' ↘ Spec (.of L)).smoothLocus))
    (hp : ∀ i, g (p' i).1 = (p i).1) :
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal
    haveI : IsProper (X' ↘ Spec (.of L)) := isProper_of_isPullback H
    haveI : ConnectedSpace X' := connectedSpace_of_isPullback_of_isSepClosed H
    (X.markedDualGraph K hnodal p).Iso (X'.markedDualGraph L hnodal' p') := by
  letI := hnodal.syntomic; have hnodal' := MorphismProperty.of_isPullback H hnodal
  letI := hnodal'.syntomic; have : IsProper (X' ↘ Spec (.of L)) := isProper_of_isPullback H
  have : ConnectedSpace X' := connectedSpace_of_isPullback_of_isSepClosed H
  have := X.isRegular_blowup_singularLocus hnodal; have := X'.isRegular_blowup_singularLocus hnodal'
  have := X.isFinite_singularLocus_subschemeι_comp hnodal
  have := X.etale_singularLocus_subschemeι_comp hnodal
  have := X.isFinite_branchSchemeToSingularLocus hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  let G := X.markedDualGraph K hnodal p; let G' := X'.markedDualGraph L hnodal' p'
  let fBl := singularLocusBlowupMap H
  let hle := Scheme.IdealSheafData.le_map_iff_comap_le.mpr
    (Scheme.singularLocus_eq_comap_of_isPullback H).ge
  let fSing := (X'.singularLocus L).subschemeMap (X.singularLocus K) g hle
  have Hsing : IsPullback fSing ((X'.singularLocus L).subschemeι ≫ (X' ↘ Spec (.of L)))
      ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (Scheme.isPullback_singularLocus_subschemeι H).flip.paste_vert H
  have hbijSing := bijective_of_isPullback_of_isFinite_of_etale Hsing
  have hbijBr := bijective_of_isPullback_of_isFinite_of_etale
    ((isPullback_branchSchemeBaseChangeMap H).paste_vert Hsing)
  let σ : G.Vertex ≃ G'.Vertex :=
    (bijOn_preimage_singularLocusBlowupMap_irreducibleComponents hnodal H).equiv
  let τ : G.Edge ≃ G'.Edge := (Equiv.ofBijective fSing hbijSing).symm
  refine
    { vertexEquiv := σ
      edgeEquiv := τ
      ends_edgeEquiv e := Sym2.ext fun w' ↦ ?_
      genus_vertexEquiv v := componentGenus_preimage_singularLocusBlowupMap hnodal H v
      vertexEquiv_marking i := ?_ }
  · rw [Sym2.mem_map]; have hfτ : fSing (τ e) = e := Equiv.ofBijective_apply_symm_apply _ hbijSing e
    refine ⟨fun hw' ↦ ⟨σ.symm w', ?_, σ.apply_symm_apply w'⟩, ?_⟩
    · obtain ⟨y', hy'w, hy'eq⟩ := (X'.mem_ends_markedDualGraph_iff hnodal' p' w' (τ e)).mp hw'
      rw [X.mem_ends_markedDualGraph_iff hnodal p]
      have hpre : fBl ⁻¹' (σ.symm w').1 = w'.1 := congrArg Subtype.val (σ.apply_symm_apply w')
      refine ⟨fBl y', mem_preimage.mp (hpre.symm ▸ hy'w), ?_⟩
      rw [← Scheme.Hom.comp_apply, singularLocusBlowupMap_blowupToBase H, Scheme.Hom.comp_apply,
        hy'eq, ← Scheme.Hom.comp_apply,
        ← (X'.singularLocus L).subschemeMap_subschemeι (X.singularLocus K) g hle,
        Scheme.Hom.comp_apply, hfτ]
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨y, hyv, hyeq⟩ := (X.mem_ends_markedDualGraph_iff hnodal p v e).mp hv
      obtain ⟨b, hbs, rfl⟩ :=
        exists_preimage_of_isPullback (X.isPullback_branchScheme K) e y hyeq.symm
      obtain ⟨b', rfl⟩ := hbijBr.surjective b
      rw [X'.mem_ends_markedDualGraph_iff hnodal' p']
      refine ⟨X'.branchSchemeToBlowup L b', ?_, ?_⟩
      · change fBl (X'.branchSchemeToBlowup L b') ∈ v.1
        rwa [← Scheme.Hom.comp_apply, ← branchSchemeBaseChangeMap_toBlowup H]
      · rw [← Scheme.Hom.comp_apply, ← X'.branchSchemeToSingularLocus_subschemeι L,
          Scheme.Hom.comp_apply]
        refine congrArg _ (hbijSing.injective ?_)
        rw [hfτ, ← Scheme.Hom.comp_apply, ← branchSchemeBaseChangeMap_toSingularLocus H,
          Scheme.Hom.comp_apply, hbs]
  · obtain ⟨y', hy'⟩ := (existsUnique_blowupToBase_eq_of_mem_smoothLocus hnodal' (p' i).2).exists
    have hy : (X.singularLocus K).blowupToBase (fBl y') = (p i).1 := by
      rw [← Scheme.Hom.comp_apply, singularLocusBlowupMap_blowupToBase H, Scheme.Hom.comp_apply,
        hy', hp i]
    symm; rw [X'.markedDualGraph_marking_eq_iff hnodal' p' i, X'.coe_blowupComponentEquiv hnodal']
    have hmem := (X.markedDualGraph_marking_eq_iff hnodal p i (G.marking i)).mp rfl
    rw [← hy, blowupToBase_mem_coe_blowupComponentEquiv_iff_of_mem_smoothLocus hnodal
      (by rw [hy]; exact (p i).2)] at hmem
    exact ⟨y', hmem, hy'⟩

@[simp]
theorem coe_markedDualGraphBaseChangeIso_vertexEquiv
    {ι : Type v} (p : ι → (letI := hnodal.syntomic; (X ↘ Spec (.of K)).smoothLocus))
    (p' : ι → (letI := (MorphismProperty.of_isPullback H hnodal).syntomic
      (X' ↘ Spec (.of L)).smoothLocus))
    (hp : ∀ i, g (p' i).1 = (p i).1) (v : (X.markedDualGraph K hnodal p).Vertex) :
    letI := hnodal.syntomic
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
    haveI : IsProper (X' ↘ Spec (.of L)) := isProper_of_isPullback H
    haveI : ConnectedSpace X' := connectedSpace_of_isPullback_of_isSepClosed H
    (((markedDualGraphBaseChangeIso hnodal H p p' hp).vertexEquiv v :
        irreducibleComponents (X'.singularLocus L).blowup) : Set (X'.singularLocus L).blowup) =
      singularLocusBlowupMap H ⁻¹' (v : Set (X.singularLocus K).blowup) := (rfl)

/-- Canonical isomorphism of unmarked dual graphs under extension of separably closed fields. -/
def dualGraphBaseChangeIso :
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal
    haveI : IsProper (X' ↘ Spec (.of L)) := isProper_of_isPullback H
    haveI : ConnectedSpace X' := connectedSpace_of_isPullback_of_isSepClosed H
    (X.dualGraph K hnodal).Iso (X'.dualGraph L hnodal') :=
  markedDualGraphBaseChangeIso hnodal H Empty.elim Empty.elim fun i ↦ i.elim

/-- Geometric rational tails are invariant under extension of a separably closed base field. -/
theorem isRationalTail_preimage_singularLocusBlowupMap_iff
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
    haveI : IsProper (X' ↘ Spec (.of L)) := isProper_of_isPullback H
    X'.IsRationalTail L hnodal'
        ⟨singularLocusBlowupMap H ⁻¹' v.1,
          (bijOn_preimage_singularLocusBlowupMap_irreducibleComponents hnodal H).mapsTo v.2⟩ ↔
      X.IsRationalTail K hnodal v := by
  have := hnodal.syntomic; have hnodal' := MorphismProperty.of_isPullback H hnodal
  have := hnodal'.syntomic; have : IsProper (X' ↘ Spec (.of L)) := isProper_of_isPullback H
  have : ConnectedSpace X' := connectedSpace_of_isPullback_of_isSepClosed H
  rw [← X'.markedDualGraph_isRationalTail_iff hnodal' Empty.elim,
    ← X.markedDualGraph_isRationalTail_iff hnodal Empty.elim]
  exact (dualGraphBaseChangeIso hnodal H).isRationalTail_vertexEquiv_iff

/-- Geometric rational bridges are invariant under extension of a separably closed base field. -/
theorem isRationalBridge_preimage_singularLocusBlowupMap_iff
    (v : letI := hnodal.syntomic; irreducibleComponents (X.singularLocus K).blowup) :
    letI := hnodal.syntomic
    haveI hnodal' := MorphismProperty.of_isPullback H hnodal; letI := hnodal'.syntomic
    haveI : IsProper (X' ↘ Spec (.of L)) := isProper_of_isPullback H
    X'.IsRationalBridge L hnodal'
        ⟨singularLocusBlowupMap H ⁻¹' v.1,
          (bijOn_preimage_singularLocusBlowupMap_irreducibleComponents hnodal H).mapsTo v.2⟩ ↔
      X.IsRationalBridge K hnodal v := by
  have := hnodal.syntomic; have hnodal' := MorphismProperty.of_isPullback H hnodal
  have := hnodal'.syntomic; have : IsProper (X' ↘ Spec (.of L)) := isProper_of_isPullback H
  have : ConnectedSpace X' := connectedSpace_of_isPullback_of_isSepClosed H
  rw [← X'.markedDualGraph_isRationalBridge_iff hnodal' Empty.elim,
    ← X.markedDualGraph_isRationalBridge_iff hnodal Empty.elim]
  exact (dualGraphBaseChangeIso hnodal H).isRationalBridge_vertexEquiv_iff

end PullbackIso

/-- Functoriality of the marked dual graph under curve isomorphisms over `Spec K`. -/
def markedDualGraphIsoOfOverIso
    {X' : Scheme.{u}} [X'.Over (Spec (.of K))] [IsProper (X' ↘ Spec (.of K))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of K)))
    (e : X' ≅ X) (he : e.hom ≫ (X ↘ Spec (.of K)) = X' ↘ Spec (.of K))
    {ι : Type v} (p : ι → (letI := hnodal.syntomic; (X ↘ Spec (.of K)).smoothLocus))
    (p' : ι → (letI := hnodal'.syntomic; (X' ↘ Spec (.of K)).smoothLocus))
    (hp : ∀ i, e.hom (p' i).1 = (p i).1) :
    (X.markedDualGraph K hnodal p).Iso (X'.markedDualGraph K hnodal' p') :=
  have H : IsPullback e.hom (X' ↘ Spec (.of K)) (X ↘ Spec (.of K)) (Spec.algebraMap K K) := by
    rw [show Spec.algebraMap K K = 𝟙 _ by rw [Spec.algebraMap, ← Spec.map_id]; rfl]
    exact IsPullback.of_horiz_isIso ⟨by simpa using he⟩
  markedDualGraphBaseChangeIso hnodal H p p' hp

/-- Functoriality of the unmarked dual graph under curve isomorphisms over `Spec K`. -/
def dualGraphIsoOfOverIso
    {X' : Scheme.{u}} [X'.Over (Spec (.of K))] [IsProper (X' ↘ Spec (.of K))] [ConnectedSpace X']
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of K)))
    (e : X' ≅ X) (he : e.hom ≫ (X ↘ Spec (.of K)) = X' ↘ Spec (.of K)) :
    (X.dualGraph K hnodal).Iso (X'.dualGraph K hnodal') :=
  markedDualGraphIsoOfOverIso hnodal hnodal' e he Empty.elim Empty.elim fun i ↦ i.elim

end DualGraphBaseChange

end AlgebraicGeometry.Scheme
