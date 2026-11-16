/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Defs

/-!
# Projections, quotients, and universal covers of the Bass–Serre tree

Building on `TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Defs`, this file relates
`X(𝔸, v₀) = 𝔸.bassSerreTree v₀` to the underlying Serre graph `Γ`:

* The `π₁(𝔸, v₀)`-invariant projections `bassSerreProj` and `bassSerreProjComponent` induce the
  quotient isomorphism `quotientBassSerreTreeIsoComponent` onto `Γ.component v₀` (and
  `quotientBassSerreTreeIso` onto `Γ` when `Γ` is preconnected).
* For `[IsEmpty Γ.E]`, `X(𝔸, v₀)` has no darts and unique vertex `𝔸.bassSerreBase v₀`.
* For `[∀ v, Subsingleton (𝔸.vertexGroup v)]`, `bassSerreVertexEquivReducedPath` identifies the
  vertices of `X(𝔸, v₀)` with reduced edge paths of `Γ` starting at `v₀`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreProj`, `TauCeti.GraphOfGroups.bassSerreProjComponent`.
* `TauCeti.GraphOfGroups.quotientBassSerreTreeHomComponent`,
  `TauCeti.GraphOfGroups.quotientBassSerreTreeIsoComponent`,
  `TauCeti.GraphOfGroups.quotientBassSerreTreeIso`.
* `TauCeti.GraphOfGroups.bassSerreVertexEquivReducedPath`.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

variable {Γ : SerreGraph.{u, v}}

/-! ### Projection and quotient graph isomorphism -/

section Quotient

variable (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- The canonical projection from the Bass–Serre tree to the underlying graph `Γ`, forgetting the
path prefix. -/
def bassSerreProj : (𝔸.bassSerreTree v₀).toSerreGraph.Hom Γ where
  mapV := bassSerreVertexProj
  mapE := bassSerreDartProj
  map_src := src_bassSerreDartProj
  map_rev := bassSerreDartProj_rev

@[simp] theorem bassSerreProj_mapV (x : (𝔸.bassSerreTree v₀).V) :
    (𝔸.bassSerreProj v₀).mapV x = bassSerreVertexProj x := (rfl)

@[simp] theorem bassSerreProj_mapE (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.bassSerreProj v₀).mapE d = bassSerreDartProj d := (rfl)

variable {𝔸 v₀} in
/-- Every vertex of `X(𝔸, v₀)` projects into the connected component of `v₀` in `Γ`. -/
theorem bassSerreVertexProj_mem_componentVertices (x : (𝔸.bassSerreTree v₀).V) :
    bassSerreVertexProj x ∈ Γ.componentVertices v₀ :=
  bassSerreVertex_induction_on x fun p => by
    rw [bassSerreVertexProj_bassSerreVertex, Γ.mem_componentVertices_iff]; exact ⟨p.edgePath⟩

variable {𝔸 v₀} in
/-- Every dart of `X(𝔸, v₀)` projects into the connected component of `v₀` in `Γ`. -/
theorem bassSerreDartProj_mem_componentDarts (d : (𝔸.bassSerreTree v₀).E) :
    bassSerreDartProj d ∈ Γ.componentDarts v₀ :=
  (Γ.mem_componentDarts_iff v₀ _).2 <|
    (Γ.mem_componentVertices_iff v₀ _).1
      (src_bassSerreDartProj d ▸ bassSerreVertexProj_mem_componentVertices _)

/-- The canonical projection from `X(𝔸, v₀)` onto the connected component `Γ.component v₀` of the
base vertex. -/
def bassSerreProjComponent : (𝔸.bassSerreTree v₀).toSerreGraph.Hom (Γ.component v₀) where
  mapV x := ⟨bassSerreVertexProj x, bassSerreVertexProj_mem_componentVertices x⟩
  mapE d := ⟨bassSerreDartProj d, bassSerreDartProj_mem_componentDarts d⟩
  map_src d := Subtype.ext (src_bassSerreDartProj d)
  map_rev d := Subtype.ext (bassSerreDartProj_rev d)

@[simp] theorem bassSerreProjComponent_mapV_val (x : (𝔸.bassSerreTree v₀).V) :
    ((𝔸.bassSerreProjComponent v₀).mapV x).1 = bassSerreVertexProj x := (rfl)

@[simp] theorem bassSerreProjComponent_mapE_val (d : (𝔸.bassSerreTree v₀).E) :
    ((𝔸.bassSerreProjComponent v₀).mapE d).1 = bassSerreDartProj d := (rfl)

@[simp] theorem bassSerreProjComponent_mapV_bassSerreBase :
    (𝔸.bassSerreProjComponent v₀).mapV (𝔸.bassSerreBase v₀) = Γ.componentBase v₀ :=
  Subtype.ext (bassSerreVertexProj_bassSerreBase.trans (Γ.componentBase_val v₀).symm)

@[simp] theorem componentInclusion_comp_bassSerreProjComponent :
    (Γ.componentInclusion v₀).comp (𝔸.bassSerreProjComponent v₀) = 𝔸.bassSerreProj v₀ := by
  ext <;> simp

private theorem bassSerreProjComponent_comp_action (g : 𝔸.π₁ v₀) :
    SerreGraph.Hom.comp (𝔸.bassSerreProjComponent v₀)
      ((𝔸.bassSerreTree v₀).action g).toHom = 𝔸.bassSerreProjComponent v₀ := by
  ext x
  · apply Subtype.ext
    simp [SerreGraph.Hom.comp_mapV, ← SerreGraph.Aut.smul_vertex_def, ← GTree.smul_vertex_def]
  · apply Subtype.ext
    simp [SerreGraph.Hom.comp_mapE, ← SerreGraph.Aut.smul_dart_def, ← GTree.smul_dart_def]

/-- The morphism from the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` to `Γ.component v₀` induced by the
`π₁(𝔸, v₀)`-invariant projection. -/
def quotientBassSerreTreeHomComponent : (𝔸.bassSerreTree v₀).quotient.Hom (Γ.component v₀) :=
  SerreGraph.quotientLift (𝔸.bassSerreTree v₀).smul_ne_rev
    (𝔸.bassSerreProjComponent v₀) (bassSerreProjComponent_comp_action 𝔸 v₀)

@[simp] theorem quotientBassSerreTreeHomComponent_comp_quotientMap :
    (𝔸.quotientBassSerreTreeHomComponent v₀).comp (𝔸.bassSerreTree v₀).quotientMap =
      𝔸.bassSerreProjComponent v₀ :=
  SerreGraph.quotientLift_comp_quotientMap ..

@[simp] theorem quotientBassSerreTreeHomComponent_mapV_quotientMap (x : (𝔸.bassSerreTree v₀).V) :
    (𝔸.quotientBassSerreTreeHomComponent v₀).mapV ((𝔸.bassSerreTree v₀).quotientMap.mapV x) =
      (𝔸.bassSerreProjComponent v₀).mapV x :=
  SerreGraph.quotientLift_mapV_quotientMap ..

@[simp] theorem quotientBassSerreTreeHomComponent_mapE_quotientMap (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.quotientBassSerreTreeHomComponent v₀).mapE ((𝔸.bassSerreTree v₀).quotientMap.mapE d) =
      (𝔸.bassSerreProjComponent v₀).mapE d :=
  SerreGraph.quotientLift_mapE_quotientMap ..

private theorem quotientBassSerreTreeHomComponent_mapV_bijective :
    Function.Bijective (𝔸.quotientBassSerreTreeHomComponent v₀).mapV := by
  refine ⟨fun y₁ y₂ h => ?_, fun ⟨v, hv⟩ => ?_⟩
  · obtain ⟨x₁, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapV_surjective y₁
    obtain ⟨x₂, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapV_surjective y₂
    induction x₁ using bassSerreVertex_induction_on with | @h v₁ p₁
    induction x₂ using bassSerreVertex_induction_on with | @h v₂ p₂
    have hv : v₁ = v₂ := by simpa using congrArg Subtype.val h
    subst hv
    refine (𝔸.bassSerreTree v₀).quotientMap_mapV_eq_iff.2 ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [mk_smul_bassSerreVertex]
    exact bassSerreVertex_congr (by simpa using Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)
  · obtain ⟨γ⟩ := (Γ.mem_componentVertices_iff v₀ v).1 hv
    refine ⟨(𝔸.bassSerreTree v₀).quotientMap.mapV
      (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)), ?_⟩
    apply Subtype.ext; simp

private theorem quotientBassSerreTreeHomComponent_mapE_bijective :
    Function.Bijective (𝔸.quotientBassSerreTreeHomComponent v₀).mapE := by
  refine ⟨fun z₁ z₂ h => ?_, fun ⟨e, he⟩ => ?_⟩
  · obtain ⟨d₁, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapE_surjective z₁
    obtain ⟨d₂, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapE_surjective z₂
    induction d₁ using bassSerreDart_induction_on with | @h v₁ v₁' p₁ e₁
    induction d₂ using bassSerreDart_induction_on with | @h v₂ v₂' p₂ e₂
    have he : e₁.1 = e₂.1 := by simpa using congrArg Subtype.val h
    have hv : v₁ = v₂ := e₁.2.1.symm.trans ((congrArg Γ.src he).trans e₂.2.1)
    have hv' : v₁' = v₂' := e₁.2.2.symm.trans ((congrArg Γ.tgt he).trans e₂.2.2)
    subst hv; subst hv'
    obtain rfl : e₁ = e₂ := Subtype.ext he
    refine (𝔸.bassSerreTree v₀).quotientMap_mapE_eq_iff.2 ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [mk_smul_bassSerreDart]
    exact bassSerreDart_congr (by simpa using Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil) e₁
  · obtain ⟨γ⟩ := (Γ.mem_componentDarts_iff v₀ e).1 he
    refine ⟨(𝔸.bassSerreTree v₀).quotientMap.mapE
      (bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e)), ?_⟩
    apply Subtype.ext; simp

/-- The quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` is canonically isomorphic to the connected component
of `v₀` in `Γ`. -/
noncomputable def quotientBassSerreTreeIsoComponent :
    (𝔸.bassSerreTree v₀).quotient.Iso (Γ.component v₀) :=
  (𝔸.quotientBassSerreTreeHomComponent v₀).toIso
    (quotientBassSerreTreeHomComponent_mapV_bijective 𝔸 v₀)
    (quotientBassSerreTreeHomComponent_mapE_bijective 𝔸 v₀)

@[simp] theorem quotientBassSerreTreeIsoComponent_toHom :
    (𝔸.quotientBassSerreTreeIsoComponent v₀).toHom = 𝔸.quotientBassSerreTreeHomComponent v₀ :=
  SerreGraph.Hom.toIso_toHom ..

@[simp] theorem quotientBassSerreTreeIsoComponent_equivV_quotientMap
    (x : (𝔸.bassSerreTree v₀).V) :
    (𝔸.quotientBassSerreTreeIsoComponent v₀).equivV
      ((𝔸.bassSerreTree v₀).quotientMap.mapV x) = (𝔸.bassSerreProjComponent v₀).mapV x := by
  rw [quotientBassSerreTreeIsoComponent, SerreGraph.Hom.toIso_equivV_apply,
    quotientBassSerreTreeHomComponent_mapV_quotientMap]

@[simp] theorem quotientBassSerreTreeIsoComponent_equivE_quotientMap
    (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.quotientBassSerreTreeIsoComponent v₀).equivE
      ((𝔸.bassSerreTree v₀).quotientMap.mapE d) = (𝔸.bassSerreProjComponent v₀).mapE d := by
  rw [quotientBassSerreTreeIsoComponent, SerreGraph.Hom.toIso_equivE_apply,
    quotientBassSerreTreeHomComponent_mapE_quotientMap]

@[simp] theorem quotientBassSerreTreeIsoComponent_equivV_symm_bassSerreProjComponent
    (x : (𝔸.bassSerreTree v₀).V) :
    (𝔸.quotientBassSerreTreeIsoComponent v₀).equivV.symm
      ((𝔸.bassSerreProjComponent v₀).mapV x) = (𝔸.bassSerreTree v₀).quotientMap.mapV x :=
  (𝔸.quotientBassSerreTreeIsoComponent v₀).equivV.symm_apply_eq.2
    (quotientBassSerreTreeIsoComponent_equivV_quotientMap 𝔸 v₀ x).symm

@[simp] theorem quotientBassSerreTreeIsoComponent_equivV_symm_componentBase :
    (𝔸.quotientBassSerreTreeIsoComponent v₀).equivV.symm (Γ.componentBase v₀) =
      (𝔸.bassSerreTree v₀).quotientMap.mapV (𝔸.bassSerreBase v₀) := by
  rw [← bassSerreProjComponent_mapV_bassSerreBase,
    quotientBassSerreTreeIsoComponent_equivV_symm_bassSerreProjComponent]

/-- Evaluating the inverse vertex equivalence of `quotientBassSerreTreeIsoComponent` on a vertex
reached from `v₀` by an edge path `γ` lifts `γ` to the Bass–Serre tree and projects to the
quotient. -/
theorem quotientBassSerreTreeIsoComponent_equivV_symm_mk {v : Γ.V} (γ : Γ.Path v₀ v) :
    (𝔸.quotientBassSerreTreeIsoComponent v₀).equivV.symm
      ⟨v, (Γ.mem_componentVertices_iff v₀ v).2 ⟨γ⟩⟩ =
      (𝔸.bassSerreTree v₀).quotientMap.mapV
        (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)) := by
  have h : (𝔸.bassSerreProjComponent v₀).mapV
      (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)) =
      ⟨v, (Γ.mem_componentVertices_iff v₀ v).2 ⟨γ⟩⟩ :=
    Subtype.ext (bassSerreVertexProj_bassSerreVertex _)
  rw [← h, quotientBassSerreTreeIsoComponent_equivV_symm_bassSerreProjComponent]

@[simp] theorem quotientBassSerreTreeIsoComponent_equivE_symm_bassSerreProjComponent
    (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.quotientBassSerreTreeIsoComponent v₀).equivE.symm
      ((𝔸.bassSerreProjComponent v₀).mapE d) = (𝔸.bassSerreTree v₀).quotientMap.mapE d :=
  (𝔸.quotientBassSerreTreeIsoComponent v₀).equivE.symm_apply_eq.2
    (quotientBassSerreTreeIsoComponent_equivE_quotientMap 𝔸 v₀ d).symm

/-- Evaluating the inverse dart equivalence of `quotientBassSerreTreeIsoComponent` on a dart `e`
whose source is reached from `v₀` by an edge path `γ` lifts `(γ, e)` to the Bass–Serre tree and
projects to the quotient. -/
theorem quotientBassSerreTreeIsoComponent_equivE_symm_mk {e : Γ.E} (γ : Γ.Path v₀ (Γ.src e)) :
    (𝔸.quotientBassSerreTreeIsoComponent v₀).equivE.symm
      ⟨e, (Γ.mem_componentDarts_iff v₀ e).2 ⟨γ⟩⟩ =
      (𝔸.bassSerreTree v₀).quotientMap.mapE
        (bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)) := by
  have h : (𝔸.bassSerreProjComponent v₀).mapE
      (bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)) =
      ⟨e, (Γ.mem_componentDarts_iff v₀ e).2 ⟨γ⟩⟩ :=
    Subtype.ext ((bassSerreDartProj_bassSerreDart _ _).trans (Γ.dart_val e))
  rw [← h, quotientBassSerreTreeIsoComponent_equivE_symm_bassSerreProjComponent]

/-- When the underlying graph `Γ` is preconnected, the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` is
canonically isomorphic to `Γ`. -/
noncomputable def quotientBassSerreTreeIso (hΓ : Γ.Preconnected) :
    (𝔸.bassSerreTree v₀).quotient.Iso Γ :=
  (𝔸.quotientBassSerreTreeIsoComponent v₀).trans (Γ.componentInclusionIso v₀ hΓ)

@[simp] theorem quotientBassSerreTreeIso_toHom (hΓ : Γ.Preconnected) :
    (𝔸.quotientBassSerreTreeIso v₀ hΓ).toHom =
      (Γ.componentInclusion v₀).comp (𝔸.quotientBassSerreTreeHomComponent v₀) := by
  simp [quotientBassSerreTreeIso]

@[simp] theorem quotientBassSerreTreeIso_equivV_quotientMap (hΓ : Γ.Preconnected)
    (x : (𝔸.bassSerreTree v₀).V) :
    (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivV ((𝔸.bassSerreTree v₀).quotientMap.mapV x) =
      bassSerreVertexProj x := by
  simp [quotientBassSerreTreeIso]

@[simp] theorem quotientBassSerreTreeIso_equivE_quotientMap (hΓ : Γ.Preconnected)
    (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivE ((𝔸.bassSerreTree v₀).quotientMap.mapE d) =
      bassSerreDartProj d := by
  simp [quotientBassSerreTreeIso]

@[simp] theorem quotientBassSerreTreeIso_equivV_symm_bassSerreVertexProj
    (hΓ : Γ.Preconnected) (x : (𝔸.bassSerreTree v₀).V) :
    (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivV.symm (bassSerreVertexProj x) =
      (𝔸.bassSerreTree v₀).quotientMap.mapV x :=
  (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivV.symm_apply_eq.2
    (quotientBassSerreTreeIso_equivV_quotientMap 𝔸 v₀ hΓ x).symm

@[simp] theorem quotientBassSerreTreeIso_equivV_symm_self (hΓ : Γ.Preconnected) :
    (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivV.symm v₀ =
      (𝔸.bassSerreTree v₀).quotientMap.mapV (𝔸.bassSerreBase v₀) :=
  (congrArg (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivV.symm
    bassSerreVertexProj_bassSerreBase.symm).trans
    (quotientBassSerreTreeIso_equivV_symm_bassSerreVertexProj 𝔸 v₀ hΓ (𝔸.bassSerreBase v₀))

@[simp] theorem quotientBassSerreTreeIso_equivE_symm_bassSerreDartProj
    (hΓ : Γ.Preconnected) (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivE.symm (bassSerreDartProj d) =
      (𝔸.bassSerreTree v₀).quotientMap.mapE d :=
  (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivE.symm_apply_eq.2
    (quotientBassSerreTreeIso_equivE_quotientMap 𝔸 v₀ hΓ d).symm

/-- For preconnected `Γ`, evaluating the inverse vertex equivalence of `quotientBassSerreTreeIso`
on a vertex reached from `v₀` by `γ` lifts `γ` to the Bass–Serre tree and projects to the
quotient. -/
theorem quotientBassSerreTreeIso_equivV_symm_of_path (hΓ : Γ.Preconnected) {v : Γ.V}
    (γ : Γ.Path v₀ v) :
    (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivV.symm v =
      (𝔸.bassSerreTree v₀).quotientMap.mapV
        (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)) :=
  (congrArg (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivV.symm
    (bassSerreVertexProj_bassSerreVertex _).symm).trans
    (quotientBassSerreTreeIso_equivV_symm_bassSerreVertexProj 𝔸 v₀ hΓ
      (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)))

/-- For preconnected `Γ`, evaluating the inverse dart equivalence of `quotientBassSerreTreeIso`
on a dart `e` whose source is reached from `v₀` by `γ` lifts `(γ, e)` to the Bass–Serre tree and
projects to the quotient. -/
theorem quotientBassSerreTreeIso_equivE_symm_of_path (hΓ : Γ.Preconnected) {e : Γ.E}
    (γ : Γ.Path v₀ (Γ.src e)) :
    (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivE.symm e =
      (𝔸.bassSerreTree v₀).quotientMap.mapE
        (bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)) :=
  (congrArg (𝔸.quotientBassSerreTreeIso v₀ hΓ).equivE.symm
    ((bassSerreDartProj_bassSerreDart _ _).trans (Γ.dart_val e)).symm).trans
    (quotientBassSerreTreeIso_equivE_symm_bassSerreDartProj 𝔸 v₀ hΓ
      (bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)))

end Quotient

/-! ### Graphs without edges -/

section IsEmpty

variable (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) [IsEmpty Γ.E]

/-- Over a graph without edges, the Bass–Serre tree has no darts. -/
instance : IsEmpty (𝔸.bassSerreTree v₀).E :=
  ⟨fun d => bassSerreDart_induction_on d fun _ e => isEmptyElim e.1⟩

/-- Over a graph without edges, the Bass–Serre tree consists of the base vertex alone. -/
instance : Unique (𝔸.bassSerreTree v₀).V where
  default := 𝔸.bassSerreBase v₀
  uniq x := @Subsingleton.elim _ (𝔸.bassSerreTree v₀).subsingleton_of_isEmpty_dart x _

end IsEmpty

/-! ### Universal cover for trivial vertex groups -/

section Subsingleton

variable (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) [∀ v, Subsingleton (𝔸.vertexGroup v)]

/-- When all vertex groups are trivial, the vertices of `X(𝔸, v₀)` correspond bijectively to the
reduced edge paths of `Γ` starting at `v₀`. -/
noncomputable def bassSerreVertexEquivReducedPath :
    (𝔸.bassSerreTree v₀).V ≃
      {q : Σ v : Γ.V, Γ.Path v₀ v // SerreGraph.Path.IsReduced Γ q.2} :=
  (Equiv.ofBijective
    (fun q : {q : Σ v : Γ.V, Γ.Path v₀ v // SerreGraph.Path.IsReduced Γ q.2} =>
      bassSerreVertex ((dartPrefunctor 𝔸).mapPath q.1.2))
    ⟨fun ⟨⟨v₁, γ₁⟩, h₁⟩ ⟨⟨v₂, γ₂⟩, h₂⟩ h => by
      have hv : v₁ = v₂ := (bassSerreVertexProj_bassSerreVertex _).symm.trans
        ((congrArg bassSerreVertexProj h).trans (bassSerreVertexProj_bassSerreVertex _))
      subst hv
      obtain ⟨g, hg⟩ := bassSerreVertex_eq_iff.1 h
      rw [Subsingleton.elim g 1] at hg
      have hhom : SerreGraph.Path.Homotopic Γ γ₁ γ₂ :=
        (Path.homotopic_mapPath_dartPrefunctor_iff (𝔸 := 𝔸)).1 (hg.trans (Path.Homotopic.one _))
      exact Subtype.ext (congrArg (Sigma.mk v₁) (hhom.eq_of_isReduced Γ h₁ h₂)),
    fun x => bassSerreVertex_induction_on x fun {v} p =>
      ⟨⟨⟨v, SerreGraph.Path.reduce Γ p.edgePath⟩, SerreGraph.Path.isReduced_reduce Γ p.edgePath⟩,
        bassSerreVertex_congr <|
          ((SerreGraph.Path.homotopic_reduce Γ p.edgePath).symm.mapPath_dartPrefunctor 𝔸).trans
            (Path.homotopic_mapPath_edgePath p).symm⟩⟩).symm

@[simp] theorem bassSerreVertexEquivReducedPath_symm_apply
    (q : {q : Σ v : Γ.V, Γ.Path v₀ v // SerreGraph.Path.IsReduced Γ q.2}) :
    (𝔸.bassSerreVertexEquivReducedPath v₀).symm q =
      bassSerreVertex ((dartPrefunctor 𝔸).mapPath q.1.2) := (rfl)

@[simp] theorem bassSerreVertexEquivReducedPath_bassSerreVertex {v : Γ.V}
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    𝔸.bassSerreVertexEquivReducedPath v₀ (bassSerreVertex p) =
      ⟨⟨v, SerreGraph.Path.reduce Γ p.edgePath⟩,
        SerreGraph.Path.isReduced_reduce Γ p.edgePath⟩ :=
  (Equiv.eq_symm_apply _).1 <| (bassSerreVertex_congr <|
    ((SerreGraph.Path.homotopic_reduce Γ p.edgePath).symm.mapPath_dartPrefunctor 𝔸).trans
      (Path.homotopic_mapPath_edgePath p).symm).symm

@[simp] theorem bassSerreVertexEquivReducedPath_bassSerreBase :
    𝔸.bassSerreVertexEquivReducedPath v₀ (𝔸.bassSerreBase v₀) =
      ⟨⟨v₀, Quiver.Path.nil⟩, SerreGraph.Path.isReduced_nil Γ v₀⟩ := by
  rw [← bassSerreVertex_nil, bassSerreVertexEquivReducedPath_bassSerreVertex]
  exact Subtype.ext (Sigma.ext rfl (by simp))

end Subsingleton

end TauCeti.GraphOfGroups
