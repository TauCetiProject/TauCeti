/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Basic

/-!
# The quotient of the Bass–Serre tree

The Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` over a Serre graph `Γ` admits a natural
`π₁(𝔸, v₀)`-invariant morphism `GraphOfGroups.bassSerreProj 𝔸 v₀` onto the connected component
`Γ.component v₀` of `v₀` in `Γ`. It descends to an isomorphism of Serre graphs
`X(𝔸, v₀) / π₁(𝔸, v₀) ≃ Γ.component v₀` (`GraphOfGroups.quotientBassSerreTreeIso`), and hence to
`X(𝔸, v₀) / π₁(𝔸, v₀) ≃ Γ` whenever `Γ` is preconnected
(`GraphOfGroups.quotientBassSerreTreeIsoOfPreconnected`).

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreProj`: the `π₁(𝔸, v₀)`-invariant morphism from `X(𝔸, v₀)` onto
  `Γ.component v₀`.
* `TauCeti.GraphOfGroups.quotientBassSerreTreeIso`: the isomorphism
  `(𝔸.bassSerreTree v₀).quotient.Iso (Γ.component v₀)`.
* `TauCeti.GraphOfGroups.quotientBassSerreTreeIsoOfPreconnected`: the isomorphism
  `(𝔸.bassSerreTree v₀).quotient.Iso Γ` when `Γ` is preconnected.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

open SerreGraph

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

private def bassSerreProjV : (𝔸.bassSerreTree v₀).V → (Γ.component v₀).V :=
  bassSerreVertexLift 𝔸 v₀
    (fun v p => (⟨v, (Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩⟩ : (Γ.component v₀).V))
    (fun _ {_ _} _ => rfl) (fun _ _ _ => rfl)

private def bassSerreProjE : (𝔸.bassSerreTree v₀).E → (Γ.component v₀).E :=
  bassSerreDartLift 𝔸 v₀
    (fun e p => (⟨e, (Γ.mem_componentDarts_iff v₀).mpr
      ((Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩)⟩ : (Γ.component v₀).E))
    (fun _ {_ _} _ => rfl) (fun _ _ _ => rfl)

private theorem bassSerreProjV_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    bassSerreProjV 𝔸 v₀ (bassSerreVertex p) =
      ⟨v, (Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩⟩ :=
  bassSerreVertexLift_vertex _ _ _ p

private theorem bassSerreProjE_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    bassSerreProjE 𝔸 v₀ (bassSerreDart e p) =
      ⟨e, (Γ.mem_componentDarts_iff v₀).mpr
        ((Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩)⟩ :=
  bassSerreDartLift_dart _ _ _ e p

/-- The `π₁(𝔸, v₀)`-invariant morphism from the Bass–Serre tree `X(𝔸, v₀)` onto the connected
component `Γ.component v₀` of `v₀` in `Γ`. -/
def bassSerreProj : (𝔸.bassSerreTree v₀).toSerreGraph.Hom (Γ.component v₀) where
  mapV := bassSerreProjV 𝔸 v₀
  mapE := bassSerreProjE 𝔸 v₀
  map_src d := by
    induction d using bassSerreDart_induction_on with | h e p =>
    rw [bassSerreTree_src_dart, bassSerreProjE_dart, bassSerreProjV_vertex]
    rfl
  map_rev d := by
    induction d using bassSerreDart_induction_on with | h e p =>
    rw [bassSerreTree_rev_dart, bassSerreProjE_dart, bassSerreProjE_dart]
    rfl

@[simp] theorem bassSerreProj_mapV_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreProj v₀).mapV (bassSerreVertex p) =
      ⟨v, (Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩⟩ :=
  bassSerreProjV_vertex 𝔸 v₀ p

theorem bassSerreProj_mapV_vertex_val {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    ((𝔸.bassSerreProj v₀).mapV (bassSerreVertex p)).1 = v := by
  rw [bassSerreProj_mapV_vertex]

@[simp] theorem bassSerreProj_mapE_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreProj v₀).mapE (bassSerreDart e p) =
      ⟨e, (Γ.mem_componentDarts_iff v₀).mpr
        ((Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩)⟩ :=
  bassSerreProjE_dart 𝔸 v₀ e p

theorem bassSerreProj_mapE_dart_val (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    ((𝔸.bassSerreProj v₀).mapE (bassSerreDart e p)).1 = e := by
  rw [bassSerreProj_mapE_dart]

/-- The projection of the Bass–Serre tree onto `Γ.component v₀` is invariant under the action of
`π₁(𝔸, v₀)`. -/
@[simp] theorem bassSerreProj_comp_action (g : π₁ 𝔸 v₀) :
    SerreGraph.Hom.comp (𝔸.bassSerreProj v₀) ((𝔸.bassSerreTree v₀).action g).toHom =
      𝔸.bassSerreProj v₀ := by
  induction g using π₁.induction_on with | h s =>
  refine SerreGraph.Hom.ext _ (funext fun x => ?_) (funext fun d => ?_)
  · induction x using bassSerreVertex_induction_on with | h p =>
    simp only [SerreGraph.Hom.comp_mapV, SerreGraph.Iso.toHom_mapV, Function.comp_apply,
      ← SerreGraph.Aut.smul_vertex_def, ← GTree.smul_vertex_def, smul_bassSerreVertex,
      bassSerreProj_mapV_vertex]
    rfl
  · induction d using bassSerreDart_induction_on with | h e p =>
    simp only [SerreGraph.Hom.comp_mapE, SerreGraph.Iso.toHom_mapE, Function.comp_apply,
      ← SerreGraph.Aut.smul_dart_def, ← GTree.smul_dart_def, smul_bassSerreDart,
      bassSerreProj_mapE_dart]
    rfl

/-- The morphism from the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` to `Γ.component v₀` induced by
`bassSerreProj`. -/
private def quotientBassSerreProj :
    (𝔸.bassSerreTree v₀).quotient.Hom (Γ.component v₀) :=
  SerreGraph.quotientLift (𝔸.bassSerreTree v₀).smul_ne_rev (𝔸.bassSerreProj v₀)
    (𝔸.bassSerreProj_comp_action v₀)

private theorem quotientBassSerreProj_mapV_bijective :
    Function.Bijective (quotientBassSerreProj 𝔸 v₀).mapV := by
  refine ⟨fun x y hxy => ?_, fun ⟨v, hv⟩ => ?_⟩
  · obtain ⟨x, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapV_surjective x
    obtain ⟨y, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapV_surjective y
    induction x using bassSerreVertex_induction_on with | @h v p =>
    induction y using bassSerreVertex_induction_on with | @h w q =>
    rw [quotientBassSerreProj, SerreGraph.quotientLift_mapV_quotientMap,
      SerreGraph.quotientLift_mapV_quotientMap] at hxy
    have hvw : v = w := by
      simpa only [bassSerreProj_mapV_vertex_val] using congrArg Subtype.val hxy
    subst hvw
    rw [GTree.quotientMap_mapV_eq_iff]
    refine ⟨π₁.mk (q.comp p.reverse), ?_⟩
    rw [smul_bassSerreVertex]
    refine bassSerreVertex_congr ?_
    rw [Quiver.Path.comp_assoc]
    simpa only [Quiver.Path.comp_nil] using (Path.Homotopic.reverse_comp p).comp_left q
  · obtain ⟨γ⟩ := (Γ.mem_componentVertices_iff v₀).mp hv
    refine ⟨(𝔸.bassSerreTree v₀).quotientMap.mapV
      (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)), ?_⟩
    rw [quotientBassSerreProj, SerreGraph.quotientLift_mapV_quotientMap, bassSerreProj_mapV_vertex]

private theorem quotientBassSerreProj_mapE_bijective :
    Function.Bijective (quotientBassSerreProj 𝔸 v₀).mapE := by
  refine ⟨fun d₁ d₂ hd => ?_, fun ⟨e, he⟩ => ?_⟩
  · obtain ⟨d₁, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapE_surjective d₁
    obtain ⟨d₂, rfl⟩ := (𝔸.bassSerreTree v₀).quotientMap_mapE_surjective d₂
    induction d₁ using bassSerreDart_induction_on with | h e₁ p =>
    induction d₂ using bassSerreDart_induction_on with | h e₂ q =>
    rw [quotientBassSerreProj, SerreGraph.quotientLift_mapE_quotientMap,
      SerreGraph.quotientLift_mapE_quotientMap] at hd
    have he : e₁ = e₂ := by
      simpa only [bassSerreProj_mapE_dart_val] using congrArg Subtype.val hd
    subst he
    rw [GTree.quotientMap_mapE_eq_iff]
    refine ⟨π₁.mk (q.comp p.reverse), ?_⟩
    rw [smul_bassSerreDart]
    refine bassSerreDart_congr ?_
    rw [Quiver.Path.comp_assoc]
    simpa only [Quiver.Path.comp_nil] using (Path.Homotopic.reverse_comp p).comp_left q
  · obtain ⟨γ⟩ := (Γ.mem_componentVertices_iff v₀).mp ((Γ.mem_componentDarts_iff v₀).mp he)
    refine ⟨(𝔸.bassSerreTree v₀).quotientMap.mapE
      (bassSerreDart e ((dartPrefunctor 𝔸).mapPath γ)), ?_⟩
    rw [quotientBassSerreProj, SerreGraph.quotientLift_mapE_quotientMap, bassSerreProj_mapE_dart]

/-- The quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` is isomorphic to the connected component of `v₀` in
the underlying graph `Γ`. -/
noncomputable def quotientBassSerreTreeIso :
    (𝔸.bassSerreTree v₀).quotient.Iso (Γ.component v₀) :=
  (quotientBassSerreProj 𝔸 v₀).toIso
    (quotientBassSerreProj_mapV_bijective 𝔸 v₀)
    (quotientBassSerreProj_mapE_bijective 𝔸 v₀)

@[simp] theorem quotientBassSerreTreeIso_equivV_quotientMap (x : (𝔸.bassSerreTree v₀).V) :
    (𝔸.quotientBassSerreTreeIso v₀).equivV ((𝔸.bassSerreTree v₀).quotientMap.mapV x) =
      (𝔸.bassSerreProj v₀).mapV x := by
  rw [quotientBassSerreTreeIso, SerreGraph.Hom.toIso_equivV_apply, quotientBassSerreProj,
    SerreGraph.quotientLift_mapV_quotientMap]

@[simp] theorem quotientBassSerreTreeIso_equivE_quotientMap (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.quotientBassSerreTreeIso v₀).equivE ((𝔸.bassSerreTree v₀).quotientMap.mapE d) =
      (𝔸.bassSerreProj v₀).mapE d := by
  rw [quotientBassSerreTreeIso, SerreGraph.Hom.toIso_equivE_apply, quotientBassSerreProj,
    SerreGraph.quotientLift_mapE_quotientMap]

@[simp] theorem quotientBassSerreTreeIso_toHom_comp_quotientMap :
    SerreGraph.Hom.comp (𝔸.quotientBassSerreTreeIso v₀).toHom (𝔸.bassSerreTree v₀).quotientMap =
      𝔸.bassSerreProj v₀ := by
  ext x <;> simp

/-- When the underlying graph `Γ` is preconnected, the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` is
isomorphic to `Γ`. -/
noncomputable def quotientBassSerreTreeIsoOfPreconnected (hΓ : Γ.Preconnected) :
    (𝔸.bassSerreTree v₀).quotient.Iso Γ :=
  (𝔸.quotientBassSerreTreeIso v₀).trans (Γ.componentIso v₀ hΓ)

@[simp] theorem quotientBassSerreTreeIsoOfPreconnected_equivV_quotientMap
    (hΓ : Γ.Preconnected) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.quotientBassSerreTreeIsoOfPreconnected v₀ hΓ).equivV
      ((𝔸.bassSerreTree v₀).quotientMap.mapV (bassSerreVertex p)) = v := by
  rw [quotientBassSerreTreeIsoOfPreconnected, SerreGraph.Iso.trans_equivV, Equiv.trans_apply,
    quotientBassSerreTreeIso_equivV_quotientMap, Γ.componentIso_equivV_apply,
    bassSerreProj_mapV_vertex_val]

@[simp] theorem quotientBassSerreTreeIsoOfPreconnected_equivE_quotientMap
    (hΓ : Γ.Preconnected) (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.quotientBassSerreTreeIsoOfPreconnected v₀ hΓ).equivE
      ((𝔸.bassSerreTree v₀).quotientMap.mapE (bassSerreDart e p)) = e := by
  rw [quotientBassSerreTreeIsoOfPreconnected, SerreGraph.Iso.trans_equivE, Equiv.trans_apply,
    quotientBassSerreTreeIso_equivE_quotientMap, Γ.componentIso_equivE_apply,
    bassSerreProj_mapE_dart_val]

end GraphOfGroups

end TauCeti
