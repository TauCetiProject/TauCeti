/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Continuous simplices in a retract of a convex set

A `TauCeti.ConvexRetract X V` presents a topological space `X` as a retract of a convex subset
of a real vector space `V`. For vertices `v : ι → X`, `TauCeti.ConvexRetract.straightSimplex`
retracts the affine simplex with vertices `embed (v i)` to `X`.
`TauCeti.ConvexRetract.cylinderSimplex` gives the straight-line homotopy between a continuous
simplex and a straight simplex. These constructions commute with continuous maps covered by
compatible affine maps.

This continuous-simplex API is independent of singular simplicial sets. Its application to
singular straightening and simplicial homotopies is developed in
`TauCeti.AlgebraicTopology.Singular.Straightening`.

## References

* W. P. Thurston, *The Geometry and Topology of Three-Manifolds*, Princeton lecture notes
  (1978–1980), Section 6.1 (straightening singular simplices in hyperbolic space).
* R. Benedetti, C. Petronio, *Lectures on Hyperbolic Geometry*, Springer Universitext (1992),
  Chapter C (straight simplices and the proof of the proportionality theorem).
-/

public section

noncomputable section

open Convexity

universe u v w

namespace TauCeti

/-- A presentation of a topological space `X` as a retract of a convex subset of a real vector
space `V`: a convex set `carrier ⊆ V`, a continuous map `embed : X → V` with values in it, and a
continuous retraction of `carrier` onto `X`, that is, a continuous map
`retraction : carrier → X` with `retraction ∘ embed = id`. -/
structure ConvexRetract (X : Type u) [TopologicalSpace X] (V : Type v) [AddCommGroup V]
    [Module ℝ V] [TopologicalSpace V] where
  /-- The convex set retracting onto the space. -/
  carrier : Set V
  /-- The set `carrier` is convex. -/
  convex : Convex ℝ carrier
  /-- The map from the space into the vector space. -/
  embed : C(X, V)
  /-- The map `embed` takes values in `carrier`. -/
  embed_mem : ∀ x, embed x ∈ carrier
  /-- The retraction of `carrier` onto the space. -/
  retraction : C(carrier, X)
  /-- The retraction is a left inverse of `embed`. -/
  retraction_embed : ∀ x, retraction ⟨embed x, embed_mem x⟩ = x

namespace ConvexRetract

attribute [local instance] ConvexSpace.ofModule

variable {X : Type u} [TopologicalSpace X] {V : Type v} [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V] (R : ConvexRetract X V) {ι κ : Type*}

/-! ### Straight simplices -/

/-- The affine simplex in `V` whose vertices are the images under `embed` of the points `v i`:
the barycentric coordinates `t` go to `∑ i, tᵢ • embed (v i)`. -/
def affineSimplex (v : ι → X) (t : StdSimplex ℝ ι) : V :=
  StdSimplex.affineMapMk (R.embed ∘ v) t

/-- The barycentric formula for the affine simplex. -/
lemma affineSimplex_def [Fintype ι] (v : ι → X) (t : StdSimplex ℝ ι) :
    R.affineSimplex v t = ∑ i, t.weights i • R.embed (v i) :=
  StdSimplex.affineMapMk_apply_eq_sum_of_fintype _ _

lemma affineSimplex_mem (v : ι → X) (t : StdSimplex ℝ ι) : R.affineSimplex v t ∈ R.carrier := by
  simp only [affineSimplex, StdSimplex.affineMapMk_apply, iConvexComb_eq_sum, Finsupp.sum]
  exact R.convex.sum_mem (fun i _ ↦ t.nonneg i) t.total fun i _ ↦ R.embed_mem (v i)

@[simp]
lemma affineSimplex_single (v : ι → X) (i : ι) :
    R.affineSimplex v (.single i) = R.embed (v i) :=
  StdSimplex.affineMapMk_single _ _

lemma affineSimplex_map (f : κ → ι) (v : ι → X) (t : StdSimplex ℝ κ) :
    R.affineSimplex v (t.map f) = R.affineSimplex (v ∘ f) t :=
  iConvexComb_map t f _

/-- A convex combination of a point of `embed`'s range and a point of an affine simplex, with the
weight of the second point given by the `1`-coordinate of the image of `t` under `α`, lies in the
convex set. These are the points of the straight-line homotopy. -/
lemma cylinderPoint_mem (x : X) (v : ι → X) (α : ι → Fin 2) (t : StdSimplex ℝ ι) :
    (1 - (t.map α).weights 1) • R.embed x + (t.map α).weights 1 • R.affineSimplex v t ∈
      R.carrier :=
  R.convex (R.embed_mem x) (R.affineSimplex_mem v t)
    (sub_nonneg.2 (StdSimplex.weights_apply_le_one _ _)) ((t.map α).nonneg 1) (sub_add_cancel 1 _)

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

lemma continuous_affineSimplex (v : ι → X) : Continuous (R.affineSimplex v) :=
  StdSimplex.continuous_of_affineMap (StdSimplex.affineMapMk (R.embed ∘ v))

/-- The **straight simplex** with vertices `v`: the retraction of the affine simplex in `V` with
vertices `embed (v i)`. -/
def straightSimplex (v : ι → X) : C(StdSimplex ℝ ι, X) where
  toFun t := R.retraction ⟨R.affineSimplex v t, R.affineSimplex_mem v t⟩
  continuous_toFun := R.retraction.continuous.comp ((R.continuous_affineSimplex v).subtype_mk _)

lemma straightSimplex_apply (v : ι → X) (t : StdSimplex ℝ ι) :
    R.straightSimplex v t = R.retraction ⟨R.affineSimplex v t, R.affineSimplex_mem v t⟩ :=
  (rfl)

/-- The vertices of the straight simplex with vertices `v` are the points `v i`. -/
@[simp]
lemma straightSimplex_single (v : ι → X) (i : ι) : R.straightSimplex v (.single i) = v i := by
  simp only [straightSimplex_apply, affineSimplex_single, R.retraction_embed]

/-- Precomposing a straight simplex with the affine map of standard simplices induced by
`f : κ → ι` gives the straight simplex with vertices `v ∘ f`. -/
lemma straightSimplex_map (f : κ → ι) (v : ι → X) (t : StdSimplex ℝ κ) :
    R.straightSimplex v (t.map f) = R.straightSimplex (v ∘ f) t := by
  simp only [straightSimplex_apply, affineSimplex_map]

/-- The singular simplex of the straight-line homotopy between a singular simplex `σ` and the
straight simplex with vertices `v`, on the simplex of the cylinder whose `Δ[1]`-component is
`α : ι → Fin 2`: at `t` it is the retraction of the point dividing the segment from
`embed (σ t)` to the affine simplex in the ratio given by the `1`-coordinate of `t` mapped along
`α`. -/
def cylinderSimplex (σ : C(StdSimplex ℝ ι, X)) (v : ι → X) (α : ι → Fin 2) :
    C(StdSimplex ℝ ι, X) where
  toFun t := R.retraction ⟨_, R.cylinderPoint_mem (σ t) v α t⟩
  continuous_toFun := by
    refine R.retraction.continuous.comp (Continuous.subtype_mk ?_ _)
    have := R.continuous_affineSimplex v
    fun_prop

lemma cylinderSimplex_apply (σ : C(StdSimplex ℝ ι, X)) (v : ι → X) (α : ι → Fin 2)
    (t : StdSimplex ℝ ι) :
    R.cylinderSimplex σ v α t = R.retraction ⟨_, R.cylinderPoint_mem (σ t) v α t⟩ :=
  (rfl)

lemma cylinderSimplex_comp_map (σ : C(StdSimplex ℝ ι, X)) (v : ι → X) (α : ι → Fin 2)
    (f : κ → ι) :
    (R.cylinderSimplex σ v α).comp ⟨_, StdSimplex.continuous_map ℝ f⟩ =
      R.cylinderSimplex (σ.comp ⟨_, StdSimplex.continuous_map ℝ f⟩) (v ∘ f) (α ∘ f) := by
  ext t
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, cylinderSimplex_apply,
    affineSimplex_map, StdSimplex.map_map]
  rfl

/-- On the bottom of the cylinder the straight-line homotopy is the singular simplex itself. -/
@[simp]
lemma cylinderSimplex_zero (σ : C(StdSimplex ℝ ι, X)) (v : ι → X) :
    R.cylinderSimplex σ v (fun _ ↦ 0) = σ := by
  ext t
  simp [cylinderSimplex_apply, R.retraction_embed]

/-- On the top of the cylinder the straight-line homotopy is the straight simplex. -/
@[simp]
lemma cylinderSimplex_one (σ : C(StdSimplex ℝ ι, X)) (v : ι → X) :
    R.cylinderSimplex σ v (fun _ ↦ 1) = R.straightSimplex v := by
  ext t
  simp [cylinderSimplex_apply, straightSimplex_apply]

/-! ### Naturality -/

section Naturality

variable {Y : Type u} [TopologicalSpace Y] {W : Type w} [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace W] {R' : ConvexRetract Y W} {g : C(X, Y)} {L : V →ᵃ[ℝ] W}

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- An affine map carrying `embed` to `embed` carries affine simplices to affine simplices. -/
lemma map_affineSimplex (hembed : ∀ x, L (R.embed x) = R'.embed (g x)) (v : ι → X)
    (t : StdSimplex ℝ ι) : L (R.affineSimplex v t) = R'.affineSimplex (g ∘ v) t := by
  have ht : ∑ i ∈ t.weights.support, t.weights i = 1 := t.total
  simp only [affineSimplex, StdSimplex.affineMapMk_apply, iConvexComb_eq_sum,
    Finsupp.sum, Function.comp_apply, ← hembed]
  rw [← Finset.affineCombination_eq_linear_combination _ _ _ ht,
    Finset.map_affineCombination _ _ _ ht, Finset.affineCombination_eq_linear_combination _ _ _ ht]
  rfl

variable [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  (hembed : ∀ x, L (R.embed x) = R'.embed (g x)) (hmaps : Set.MapsTo L R.carrier R'.carrier)
  (hret : ∀ v (hv : v ∈ R.carrier), R'.retraction ⟨L v, hmaps hv⟩ = g (R.retraction ⟨v, hv⟩))
include hembed hret

/-- A map covered by a compatible affine map carries straight simplices to straight simplices. -/
lemma comp_straightSimplex (v : ι → X) :
    g.comp (R.straightSimplex v) = R'.straightSimplex (g ∘ v) := by
  ext t
  simp only [ContinuousMap.comp_apply, straightSimplex_apply, ← hret, R.map_affineSimplex hembed]

/-- A map covered by a compatible affine map commutes with the straight-line homotopy. -/
lemma comp_cylinderSimplex (σ : C(StdSimplex ℝ ι, X)) (v : ι → X) (α : ι → Fin 2) :
    g.comp (R.cylinderSimplex σ v α) = R'.cylinderSimplex (g.comp σ) (g ∘ v) α := by
  ext t
  simp only [ContinuousMap.comp_apply, cylinderSimplex_apply, ← hret]
  congr 2
  rw [← AffineMap.lineMap_apply_module, AffineMap.apply_lineMap, AffineMap.lineMap_apply_module,
    hembed, R.map_affineSimplex hembed]

end Naturality

end ConvexRetract

end TauCeti
