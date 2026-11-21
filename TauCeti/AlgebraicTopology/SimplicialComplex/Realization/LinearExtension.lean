/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map

/-!
# Linear extension of vertex data over a realization

A family `p : ι → E` of points of a real vector space, indexed by the vertices of an abstract
simplicial complex `K`, extends to the map `K.linearExtension p : |K| → E` sending a point with
barycentric coordinates `x` to the combination `∑ v, x v • p v`. It takes the value `p v` at the
vertex `v`, is linear in barycentric coordinates on every closed simplex, and is continuous as soon
as addition and real scalar multiplication on `E` are.

This is the common construction behind secant maps of maps out of a realization, where
`p = f ∘ vertex K`, and behind the comparison map from the realization of the vertex scheme of a
geometric complex to its ambient space, where `p` is the inclusion of the vertices.

## Main definitions

* `AbstractSimplicialComplex.linearExtension K p`: the extension of `p` linear in barycentric
  coordinates on every closed simplex.
* `AbstractSimplicialComplex.secantMap K f`: the secant map of `f : Realization K → E`, the
  linear extension of its values at the vertices.

## Main results

* `AbstractSimplicialComplex.linearExtension_vertex`: the extension takes the value `p v` at the
  vertex `v`.
* `AbstractSimplicialComplex.linearExtension_faceInclusion`: on a closed simplex the extension is
  the combination of the values of `p` at its vertices.
* `AbstractSimplicialComplex.eq_linearExtension`: uniqueness from the formula on each closed face.
* `AbstractSimplicialComplex.linearExtension_realizationMap`: naturality under simplicial maps.
* `AbstractSimplicialComplex.continuous_linearExtension`: the extension is continuous.
* `AbstractSimplicialComplex.secantMap_linearExtension`: taking the secant map fixes linear
  extensions.
* `AbstractSimplicialComplex.eq_secantMap`: a map that is linear in barycentric coordinates on
  every closed simplex, with the same vertex values as `f`, is the secant map of `f`.
* `AbstractSimplicialComplex.secantMap_eq_self_iff`: a map is its own secant map exactly when it is
  linear in barycentric coordinates on every closed simplex.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial maps and their linear extensions).
-/

public section

noncomputable section

open Set Function TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} {E : Type*} [AddCommMonoid E] [Module ℝ E] (K : AbstractSimplicialComplex ι)

/-- The extension of vertex data `p : ι → E` over the realization of `K`, sending a point with
barycentric coordinates `x` to the combination `∑ v, x v • p v`. -/
def linearExtension (p : ι → E) (x : Realization K) : E :=
  Finsupp.linearCombination ℝ p x.val

variable {K}

/-- The linear extension evaluates the barycentric coordinates as a linear combination of the
vertex data. -/
theorem linearExtension_apply (p : ι → E) (x : Realization K) :
    K.linearExtension p x = Finsupp.linearCombination ℝ p x.val :=
  (rfl)

/-- The linear extension takes the value `p v` at the vertex `v`. -/
@[simp]
theorem linearExtension_vertex (p : ι → E) (v : ι) : K.linearExtension p (vertex K v) = p v := by
  simp [linearExtension_apply]

/-- If the barycentric support of a point lies in a finite vertex set `σ`, the linear extension
at that point is the combination of the values of `p` at the vertices of `σ`. -/
theorem linearExtension_eq_sum_of_support_subset (p : ι → E) {σ : Finset ι} {x : Realization K}
    (hx : x.val.support ⊆ σ) : K.linearExtension p x = ∑ a : σ, x.val a • p a := by
  rw [linearExtension_apply, Finsupp.linearCombination_apply_of_mem_supported ℝ hx]
  exact (Finset.sum_coe_sort σ fun a => x.val a • p a).symm

/-- On a closed simplex `σ`, the linear extension is the combination of the values of `p` at the
vertices of `σ`, weighted by the barycentric coordinates. -/
theorem linearExtension_faceInclusion (p : ι → E) (σ : Face K) (x : StandardSimplex σ.val) :
    K.linearExtension p (faceInclusion K σ x) = ∑ a : σ.val, x.val a • p a := by
  have hx := (mem_range_faceInclusion_iff K σ _).mp (Set.mem_range_self x)
  rw [linearExtension_eq_sum_of_support_subset p hx, faceInclusion_val]

/-- The linear extension of vertex data into a space with continuous addition and continuous real
scalar multiplication is continuous for the weak topology on the realization. -/
theorem continuous_linearExtension [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (p : ι → E) : Continuous (K.linearExtension p) := by
  refine continuous_iff_faceInclusion.mpr fun σ => ?_
  have hcoord (a : ι) : Continuous fun x : StandardSimplex σ.val => x.val a :=
    (continuous_apply a).comp continuous_induced_dom
  simp_rw [comp_def, linearExtension_faceInclusion]
  exact continuous_finsetSum _ fun a _ => (hcoord a).smul continuous_const

/-- A map with the prescribed barycentric formula on each closed face is the linear extension
of its vertex data. -/
theorem eq_linearExtension {p : ι → E} {g : Realization K → E}
    (hg : ∀ (σ : Face K) (x : StandardSimplex σ.val),
      g (faceInclusion K σ x) = ∑ a : σ.val, x.val a • p a) :
    g = K.linearExtension p := by
  funext x
  obtain ⟨y, hy⟩ := (mem_range_faceInclusion_iff K (carrier K x) x).mpr
    (carrier_val K x).symm.subset
  calc
    g x = g (faceInclusion K (carrier K x) y) := congrArg g hy.symm
    _ = K.linearExtension p (faceInclusion K (carrier K x) y) := by
      rw [hg, linearExtension_faceInclusion]
    _ = K.linearExtension p x := congrArg (K.linearExtension p) hy

/-- Pulling a linear extension back along a simplicial realization map pulls back vertex data. -/
theorem linearExtension_realizationMap {κ : Type*} [DecidableEq κ]
    {L : AbstractSimplicialComplex κ}
    (f : PreAbstractSimplicialComplex.SimplicialMap
      K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (p : κ → E) (x : Realization K) :
    L.linearExtension p (f.realizationMap x) = K.linearExtension (p ∘ f) x := by
  rw [linearExtension_apply, linearExtension_apply,
    PreAbstractSimplicialComplex.SimplicialMap.realizationMap_val,
    Finsupp.linearCombination_mapDomain]

variable (K)

/-- The secant map of `f : |K| → E`: the map which agrees with `f` at the vertices of `K` and is
linear in barycentric coordinates on every closed simplex, the linear extension of the values of
`f` at the vertices. -/
def secantMap (f : Realization K → E) (x : Realization K) : E :=
  K.linearExtension (fun v => f (vertex K v)) x

variable {K}

/-- The secant map evaluates a point of the realization as the combination, with its
barycentric coordinates as weights, of the values of `f` at the vertices. -/
theorem secantMap_apply (f : Realization K → E) (x : Realization K) :
    K.secantMap f x = x.val.sum fun v t => t • f (vertex K v) :=
  (linearExtension_apply _ x).trans (Finsupp.linearCombination_apply ℝ x.val)

/-- The secant map agrees with `f` at every vertex. -/
@[simp]
theorem secantMap_vertex (f : Realization K → E) (v : ι) :
    K.secantMap f (vertex K v) = f (vertex K v) :=
  linearExtension_vertex _ v

/-- On a closed simplex `σ`, the secant map is the combination of the values of `f` at the
vertices of `σ`, weighted by the barycentric coordinates. -/
theorem secantMap_faceInclusion (f : Realization K → E) (σ : Face K) (x : StandardSimplex σ.val) :
    K.secantMap f (faceInclusion K σ x) = ∑ a : σ.val, x.val a • f (vertex K a) :=
  linearExtension_faceInclusion _ σ x

/-- The secant map is continuous. -/
theorem continuous_secantMap [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (f : Realization K → E) : Continuous (K.secantMap f) :=
  continuous_linearExtension _

/-- The secant map of a linear extension is that extension. -/
@[simp]
theorem secantMap_linearExtension (p : ι → E) :
    K.secantMap (K.linearExtension p) = K.linearExtension p := by
  funext x
  simp only [secantMap, linearExtension_vertex]

/-- Taking secant maps is idempotent. -/
@[simp]
theorem secantMap_secantMap (f : Realization K → E) :
    K.secantMap (K.secantMap f) = K.secantMap f :=
  secantMap_linearExtension _

/-- **Uniqueness of secant maps.** A map that is linear in barycentric coordinates on every closed
simplex, and agrees with `f` at the vertices, is the secant map of `f`. -/
theorem eq_secantMap {f g : Realization K → E}
    (hg : ∀ (σ : Face K) (x : StandardSimplex σ.val),
      g (faceInclusion K σ x) = ∑ a : σ.val, x.val a • g (vertex K a))
    (hfg : ∀ v : ι, g (vertex K v) = f (vertex K v)) :
    g = K.secantMap f :=
  eq_linearExtension fun σ x => by simp only [hg, hfg]

/-- A map is its own secant map exactly when it is linear in barycentric coordinates on every
closed simplex. -/
theorem secantMap_eq_self_iff {g : Realization K → E} :
    K.secantMap g = g ↔ ∀ (σ : Face K) (x : StandardSimplex σ.val),
      g (faceInclusion K σ x) = ∑ a : σ.val, x.val a • g (vertex K a) :=
  ⟨fun h σ x => by
    conv_lhs => rw [← h]
    exact secantMap_faceInclusion g σ x,
   fun hg => (eq_secantMap hg fun _ => rfl).symm⟩

end AbstractSimplicialComplex
