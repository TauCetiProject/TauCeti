/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps
public import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Realization of simplicial maps

A simplicial vertex map extends affinely over each closed simplex to a continuous map of weak
realizations. Coordinates of vertices with the same image are added, so injectivity of the vertex
map is unnecessary. Identity and composition are preserved, and mutually inverse simplicial maps
induce a homeomorphism. These maps transport simplicial local models and their relabelings to the
polyhedra used in triangulations and piecewise-linear charts.

For a vertex map `f`, the barycentric coordinate at a target vertex `b` is the sum of the
source coordinates over vertices sent to `b`. On each face, the induced map is the affine
extension of `f` into the simplex on the image vertex set; `realizationMap_comp_faceInclusion`
characterizes this restriction. The induced map is injective exactly when the vertex map is.

## Main definitions

* `AbstractSimplicialComplex.StandardSimplex.map`: affine pushforward on a closed simplex.
* `AbstractSimplicialComplex.StandardSimplex.comap`: the inverse affine pullback for an injective
  vertex map, used to identify polyhedra under relabeling.
* `PreAbstractSimplicialComplex.SimplicialMap.realizationMap`: the induced continuous map.
* `PreAbstractSimplicialComplex.SimplicialMap.realizationHomeomorph`: the homeomorphism induced by
  mutually inverse simplicial maps.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex.StandardSimplex

variable {α β : Type*} [DecidableEq β] {σ : Finset α}

/-- Push barycentric coordinates forward along a vertex map, adding weights when vertices are
identified. The resulting point lies in the simplex on the image vertex set. -/
def map (x : StandardSimplex σ) (f : α → β) : StandardSimplex (σ.image f) :=
  -- Mathlib's `Finsupp.lmapDomain` and `LinearMap.image_convexHull` give the simplex image.
  ⟨Finsupp.mapDomain f x.1, by
    classical
    have h := mem_image_of_mem (Finsupp.lmapDomain ℝ ℝ f) x.2
    rw [(Finsupp.lmapDomain ℝ ℝ f).image_convexHull] at h
    simpa only [Finset.coe_image, image_image, Function.comp_def,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using h⟩

/-- The affine simplex map pushes forward its finitely supported coordinate vector. -/
@[simp]
theorem map_val (x : StandardSimplex σ) (f : α → β) :
    (StandardSimplex.map x f : β →₀ ℝ) = Finsupp.mapDomain f x.1 := (rfl)

/-- A target barycentric coordinate is the sum of the source coordinates mapping to it. -/
theorem map_apply (x : StandardSimplex σ) (f : α → β) (b : β) :
    (StandardSimplex.map x f : β →₀ ℝ) b = ∑ a ∈ σ, if f a = b then x.1 a else 0 := by
  classical
  rw [map_val, Finsupp.mapDomain_apply, Finsupp.sum_of_support_subset x.1
    (StandardSimplex.support_subset x)]
  all_goals simp [Finsupp.single_apply]

/-- Affine pushforward between closed simplices is continuous for their coordinate topologies. -/
theorem continuous_map (f : α → β) :
    Continuous (fun x : StandardSimplex σ => StandardSimplex.map x f) := by
  classical
  -- The finite-face comparison transports Mathlib's `Convexity.StdSimplex.continuous_map`.
  let g : σ → σ.image f := fun a => ⟨f a, Finset.mem_image_of_mem f a.2⟩
  have h : Continuous (fun x : StandardSimplex σ =>
      (Finset.standardSimplexHomeomorph (σ.image f)).symm
        ((Finset.standardSimplexHomeomorph σ x).map g)) :=
    (Finset.standardSimplexHomeomorph (σ.image f)).symm.continuous.comp
      ((Convexity.StdSimplex.continuous_map ℝ g).comp
        (Finset.standardSimplexHomeomorph σ).continuous)
  convert h using 1
  funext x
  apply Subtype.ext
  rw [map_val, Finset.standardSimplexHomeomorph_symm_val, Convexity.StdSimplex.weights_map,
    ← Finsupp.mapDomain_comp]
  have hg : (Subtype.val : σ.image f → β) ∘ g = f ∘ (Subtype.val : σ → α) := rfl
  rw [hg, Finsupp.mapDomain_comp, ← Finset.standardSimplexHomeomorph_symm_val,
    Homeomorph.symm_apply_apply]

/-- Pull barycentric coordinates back along an injective vertex map. This is the inverse of
its affine pushforward on the simplex spanned by its image. -/
def comap {f : α ↪ β} (x : StandardSimplex (σ.image f)) : StandardSimplex σ :=
  ⟨Finsupp.comapDomain f x.1 f.injective.injOn, by
    classical
    have h := mem_image_of_mem (Finsupp.lcomapDomain (R := ℝ) (M := ℝ) f f.injective) x.2
    rw [(Finsupp.lcomapDomain f f.injective).image_convexHull] at h
    simpa only [Finset.coe_image, image_image, Function.comp_def,
      Finsupp.lcomapDomain_apply, Finsupp.comapDomain_single] using h⟩

/-- Pullback of a simplex point pulls back its finitely supported coordinate vector. -/
@[simp]
theorem comap_val {f : α ↪ β} (x : StandardSimplex (σ.image f)) :
    (comap (f := f) x : α →₀ ℝ) = Finsupp.comapDomain f x.1 f.injective.injOn := (rfl)

/-- Pulling coordinates back after pushing them forward recovers a simplex point. -/
@[simp]
theorem comap_map (x : StandardSimplex σ) (f : α ↪ β) : comap (map x f) = x := by
  apply Subtype.ext
  rw [comap_val, map_val]
  exact Finsupp.comapDomain_mapDomain f f.injective _

/-- Pushing coordinates forward after pulling them back recovers an image-simplex point. -/
@[simp]
theorem map_comap {f : α ↪ β} (x : StandardSimplex (σ.image f)) : map (comap (f := f) x) f = x := by
  apply Subtype.ext
  rw [map_val, comap_val]
  exact Finsupp.mapDomain_comapDomain f f.injective x.1 fun b hb => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (support_subset x hb)
    exact mem_range_self a

/-- Affine pullback between coordinate simplices is continuous, including on empty simplices. -/
theorem continuous_comap (f : α ↪ β) :
    Continuous (fun x : StandardSimplex (σ.image f) => comap (f := f) x) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  have hc : Continuous (fun x : StandardSimplex (σ.image f) => (x.1 : β → ℝ)) :=
    continuous_induced_dom
  simpa only [Function.comp_def, comap_val, Finsupp.comapDomain_apply] using
    (continuous_apply (f a)).comp hc

end AbstractSimplicialComplex.StandardSimplex

namespace PreAbstractSimplicialComplex.SimplicialMap

open AbstractSimplicialComplex

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
  {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}
  {P : AbstractSimplicialComplex γ}

/-- The continuous map of weak realizations induced by a simplicial map, affine on each face. -/
def realizationMap
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex) :
    C(Realization K, Realization L) where
  toFun x :=
    faceInclusion L ⟨(carrier K x).1.image f, f.map_face (carrier K x).2⟩
      (StandardSimplex.map ⟨x.1, mem_convexHull_carrier K x⟩ f)
  continuous_toFun := by
    -- Follow `AbstractSimplicialComplex.continuous_barycentricSubdivisionRealizationMap`:
    -- test continuity face by face in the weak topology.
    apply continuous_iff_faceInclusion.2
    intro σ
    convert (continuous_faceInclusion L ⟨σ.1.image f, f.map_face σ.2⟩).comp
      (StandardSimplex.continuous_map f (σ := σ.1)) using 1
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, faceInclusion_val, StandardSimplex.map_val]

/-- The induced map pushes forward barycentric coordinates, adding weights over each vertex
fiber. -/
@[simp]
theorem realizationMap_val
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (x : Realization K) :
    (f.realizationMap x : β →₀ ℝ) = Finsupp.mapDomain f x.1 :=
  by simp only [realizationMap, ContinuousMap.coe_mk, faceInclusion_val, StandardSimplex.map_val]

/-- Restriction of the realization map to a face is its affine simplex map followed by the target
face inclusion. -/
theorem realizationMap_comp_faceInclusion
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (σ : Face K) :
    f.realizationMap ∘ faceInclusion K σ =
      faceInclusion L ⟨σ.1.image f, f.map_face σ.2⟩ ∘ fun x => StandardSimplex.map x f :=
  by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, realizationMap_val, faceInclusion_val, StandardSimplex.map_val]

/-- A simplicial map sends each realization vertex to the realization of its image vertex. -/
@[simp]
theorem realizationMap_vertex
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (a : α) : f.realizationMap (vertex K a) = vertex L (f a) := by
  apply Subtype.ext
  simp only [realizationMap_val, vertex_val, Finsupp.mapDomain_single]

/-- Realization preserves the identity simplicial map. -/
@[simp]
theorem realizationMap_id [DecidableEq α] :
    (id K.toPreAbstractSimplicialComplex).realizationMap = ContinuousMap.id (Realization K) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  simp only [realizationMap_val, coe_id, Finsupp.mapDomain_id, ContinuousMap.id_apply]

/-- Realization preserves composition of simplicial maps. -/
@[simp]
theorem realizationMap_comp
    (g : SimplicialMap L.toPreAbstractSimplicialComplex P.toPreAbstractSimplicialComplex)
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex) :
    (g.comp f).realizationMap = g.realizationMap.comp f.realizationMap := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  simp only [realizationMap_val, coe_comp, Finsupp.mapDomain_comp, ContinuousMap.comp_apply]

/-- The simplicial realization of an inclusion agrees with the inclusion of polyhedra. -/
@[simp]
theorem realizationMap_inclusion [DecidableEq α] {L : AbstractSimplicialComplex α} (h : K ≤ L) :
    ⇑(inclusion h).realizationMap = AbstractSimplicialComplex.realizationMap h := by
  funext x
  apply Subtype.ext
  simp only [realizationMap_val, coe_inclusion, Finsupp.mapDomain_id,
    AbstractSimplicialComplex.realizationMap_val]

/-- The realization map is injective exactly when its vertex map is injective. -/
theorem realizationMap_injective_iff
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex) :
    Function.Injective f.realizationMap ↔ Function.Injective f := by
  constructor
  · intro h a b hab
    apply vertex_injective K
    apply h
    simp only [realizationMap_vertex, hab]
  · intro hf x y hxy
    apply Subtype.ext
    apply Finsupp.mapDomain_injective hf
    simpa only [realizationMap_val] using congrArg Subtype.val hxy

variable [DecidableEq α]

/-- Mutually inverse simplicial maps induce a homeomorphism of their weak realizations. -/
def realizationHomeomorph
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (g : SimplicialMap L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
    (hgf : g.comp f = id K.toPreAbstractSimplicialComplex)
    (hfg : f.comp g = id L.toPreAbstractSimplicialComplex) :
    Realization K ≃ₜ Realization L where
  toFun := f.realizationMap
  invFun := g.realizationMap
  left_inv x := by
    have h := congrArg (fun m => m.realizationMap x) hgf
    simpa only [realizationMap_comp, ContinuousMap.comp_apply, realizationMap_id,
      ContinuousMap.id_apply] using h
  right_inv x := by
    have h := congrArg (fun m => m.realizationMap x) hfg
    simpa only [realizationMap_comp, ContinuousMap.comp_apply, realizationMap_id,
      ContinuousMap.id_apply] using h
  continuous_toFun := f.realizationMap.continuous
  continuous_invFun := g.realizationMap.continuous

/-- The forward map of the realization homeomorphism is the given simplicial realization map. -/
@[simp]
theorem realizationHomeomorph_apply
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (g : SimplicialMap L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
    (hgf : g.comp f = id K.toPreAbstractSimplicialComplex)
    (hfg : f.comp g = id L.toPreAbstractSimplicialComplex) (x : Realization K) :
    f.realizationHomeomorph g hgf hfg x = f.realizationMap x := (rfl)

/-- The inverse of the realization homeomorphism is the inverse simplicial realization map. -/
@[simp]
theorem realizationHomeomorph_symm_apply
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (g : SimplicialMap L.toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex)
    (hgf : g.comp f = id K.toPreAbstractSimplicialComplex)
    (hfg : f.comp g = id L.toPreAbstractSimplicialComplex) (x : Realization L) :
    (f.realizationHomeomorph g hgf hfg).symm x = g.realizationMap x := (rfl)

end PreAbstractSimplicialComplex.SimplicialMap
