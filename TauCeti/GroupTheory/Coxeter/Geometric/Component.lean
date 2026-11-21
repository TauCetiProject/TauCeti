/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.GroupTheory.Coxeter.Graph
public import TauCeti.GroupTheory.Coxeter.Geometric.Basic
import TauCeti.Data.Finsupp.MapDomain

/-!
# The canonical form over the components of the Coxeter graph

Let `M` be a Coxeter matrix on an arbitrary index type `B`, and let `B(x, y)` be its canonical
bilinear form on `B →₀ ℝ` (`CoxeterMatrix.geometricForm`), with `B(αᵢ, αⱼ) = -cos (π / M i j)`.
Two distinct indices that are not adjacent in the Coxeter graph (`CoxeterMatrix.graph`) have
`M i j = 2`, so their simple roots are orthogonal, `-cos (π / 2) = 0`. Hence the form splits over
the connected components of the Coxeter graph: writing `M_K` for the restriction of `M` to a
component `K` (`CoxeterMatrix.restrict`), `B_K` for its canonical form and `x_K` for the
restriction of `x` to `K`,

`B(x, y) = ∑_K B_K(x_K, y_K)`,

a finite sum over any finite set of components containing those that meet the support of `x`
(`CoxeterMatrix.geometricForm_eq_sum_connectedComponent`). Consequently `B` is positive definite
if and only if every `B_K` is (`CoxeterMatrix.geometricForm_posDef_iff_forall_connectedComponent`).
Both statements hold more generally for any map `c : B → ι` whose distinct fibres are joined only
by entries `2`, with the fibres of `c` in place of the components. The Coxeter graph of `M_K` is
the induced graph on `K` (`CoxeterMatrix.graph_restrict`), and is connected
(`CoxeterMatrix.connected_graph_restrict_supp`). The decomposition
rests on the orthogonality `CoxeterMatrix.geometricForm_eq_zero_of_eq_two` and on the description
`CoxeterMatrix.geometricForm_restrict` of the canonical form of a restriction.

For a finite index type `B`, the Coxeter group is finite if and only if its canonical form is
positive definite. Together with this criterion, the results here reduce the classification of
finite Coxeter groups of finite rank to Coxeter matrices with connected Coxeter graph. Without
finiteness of `B` positive definiteness does not imply finiteness of the group, for instance for
infinitely many pairwise commuting generators.

## Main results

* `CoxeterMatrix.geometricForm_eq_sum_restrict` and
  `CoxeterMatrix.geometricForm_eq_sum_connectedComponent`: the canonical form is the sum of the
  canonical forms of the restrictions to the fibres, in particular to the connected components.
* `CoxeterMatrix.geometricForm_posDef_iff_of_eq_two` and
  `CoxeterMatrix.geometricForm_posDef_iff_forall_connectedComponent`: the canonical form is
  positive definite if and only if it is on every fibre, in particular on every component.

## References

* M. W. Davis, *The Geometry and Topology of Coxeter Groups*, London Mathematical Society
  Monographs 32, Princeton University Press (2008), Definition 3.5.1 and §C.1.
-/

public section

open Real

namespace CoxeterMatrix

variable {B : Type*} (M : CoxeterMatrix B)

/-- The canonical form of the restriction to `J`, evaluated on restrictions, is the canonical form
of the parts supported on `J`. -/
private theorem geometricForm_restrict_subtypeDomain (J : Set B) [DecidablePred (· ∈ J)]
    (x y : B →₀ ℝ) :
    (M.restrict J).geometricForm (x.subtypeDomain (· ∈ J)) (y.subtypeDomain (· ∈ J)) =
      M.geometricForm (x.filter (· ∈ J)) (y.filter (· ∈ J)) := by
  rw [geometricForm_restrict, Finsupp.mapDomain_subtypeDomain_eq_filter,
    Finsupp.mapDomain_subtypeDomain_eq_filter]

/-! ### The decomposition of the form -/

/-- For `c : B → ι` whose distinct fibres are joined only by entries `2`, the canonical form is the
sum of the canonical forms of the parts supported on the fibres. -/
private theorem geometricForm_eq_sum_filter {ι : Type*} [DecidableEq ι] (c : B → ι)
    (hc : ∀ i j, c i ≠ c j → M i j = 2) {s : Finset ι} {x : B →₀ ℝ}
    (hs : ∀ i ∈ x.support, c i ∈ s) (y : B →₀ ℝ) :
    M.geometricForm x y =
      ∑ k ∈ s, M.geometricForm (x.filter (c · = k)) (y.filter (c · = k)) := by
  -- `x` is the sum of its parts on the fibres over `s`.
  have hxs : x = ∑ k ∈ s, x.filter (c · = k) := by
    ext i
    simp only [Finsupp.finsetSum_apply, Finsupp.filter_apply]
    rw [Finset.sum_ite_eq]
    split_ifs with hi
    · rfl
    · exact Finsupp.notMem_support_iff.mp fun h ↦ hi (hs i h)
  conv_lhs => rw [hxs]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  -- The part of `x` on the fibre over `k` is orthogonal to the part of `y` off that fibre.
  conv_lhs => rw [← Finsupp.filter_add_filter_not y (c · = k)]
  rw [map_add, M.geometricForm_eq_zero_of_eq_two (y := y.filter fun i ↦ ¬c i = k), add_zero]
  intro i hi j hj
  rw [Finsupp.support_filter, Finset.mem_filter] at hi hj
  exact hc i j (hi.2.trans_ne fun h ↦ hj.2 h.symm)

/-- **The canonical form splits over the fibres of a map** `c : B → ι` whose distinct fibres are
joined only by entries `2`: `B(x, y)` is the sum over `k ∈ s` of the canonical forms of the
restrictions of `M`, `x` and `y` to the fibre over `k`, for any finite set `s` containing the
images under `c` of the support of `x`. -/
theorem geometricForm_eq_sum_restrict {ι : Type*} (c : B → ι)
    (hc : ∀ i j, c i ≠ c j → M i j = 2) {s : Finset ι} {x : B →₀ ℝ}
    (hs : ∀ i ∈ x.support, c i ∈ s) (y : B →₀ ℝ) :
    M.geometricForm x y =
      ∑ k ∈ s, (M.restrict (c ⁻¹' {k})).geometricForm (x.subtypeDomain (· ∈ c ⁻¹' {k}))
        (y.subtypeDomain (· ∈ c ⁻¹' {k})) := by
  classical
  rw [M.geometricForm_eq_sum_filter c hc hs y]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [geometricForm_restrict_subtypeDomain]
  -- `i ∈ c ⁻¹' {k}` unfolds to `c i = k` (`Set.mem_preimage`, `Set.mem_singleton_iff`, both
  -- `Iff.rfl`), so the two filters agree.
  rfl

/-- **The canonical form splits over the connected components of the Coxeter graph**:
`B(x, y) = ∑_K B_K(x_K, y_K)`, where `B_K` is the canonical form of the restriction of `M` to the
component `K` and `x_K`, `y_K` are the restrictions of `x`, `y` to `K`. The sum runs over any finite
set of components containing every component that meets the support of `x`, for instance their
image `x.support.image M.graph.connectedComponentMk`. -/
theorem geometricForm_eq_sum_connectedComponent {s : Finset M.graph.ConnectedComponent}
    {x : B →₀ ℝ} (hs : ∀ i ∈ x.support, M.graph.connectedComponentMk i ∈ s) (y : B →₀ ℝ) :
    M.geometricForm x y =
      ∑ K ∈ s, (M.restrict K.supp).geometricForm (x.subtypeDomain (· ∈ K.supp))
        (y.subtypeDomain (· ∈ K.supp)) :=
  M.geometricForm_eq_sum_restrict _ (fun _ _ ↦ M.eq_two_of_connectedComponentMk_ne) hs y

/-! ### Positive definiteness -/

/-- **The canonical form is positive definite if and only if it is on every fibre** of a map
`c : B → ι` whose distinct fibres are joined only by entries `2`. -/
theorem geometricForm_posDef_iff_of_eq_two {ι : Type*} (c : B → ι)
    (hc : ∀ i j, c i ≠ c j → M i j = 2) :
    M.geometricForm.toQuadraticMap.PosDef ↔
      ∀ k, (M.restrict (c ⁻¹' {k})).geometricForm.toQuadraticMap.PosDef := by
  classical
  refine ⟨fun hB k u hu ↦ ?_, fun hB x hx ↦ ?_⟩
  · -- Extension by zero is injective and pulls the canonical form back to the restricted one.
    have hu' : u.mapDomain Subtype.val ≠ 0 :=
      (Finsupp.mapDomain_injective Subtype.val_injective).ne_iff' Finsupp.mapDomain_zero |>.mpr hu
    simpa [geometricForm_restrict] using hB _ hu'
  · -- Each fibre contributes a nonnegative term, and the fibre of a point of the support of `x`
    -- a positive one.
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
    rw [LinearMap.BilinMap.toQuadraticMap_apply,
      M.geometricForm_eq_sum_restrict c hc (s := x.support.image c)
        (fun j hj ↦ Finset.mem_image_of_mem c hj)]
    refine Finset.sum_pos' (fun k _ ↦ (hB k).nonneg _) ⟨c i, Finset.mem_image_of_mem c hi, ?_⟩
    refine hB (c i) _ fun h ↦ Finsupp.mem_support_iff.mp hi ?_
    simpa using DFunLike.congr_fun h ⟨i, rfl⟩

/-- **The canonical form is positive definite if and only if it is on every connected component
of the Coxeter graph**: `B` is positive definite exactly when, for every component `K`, the
canonical form of the restriction of `M` to `K` is. -/
theorem geometricForm_posDef_iff_forall_connectedComponent :
    M.geometricForm.toQuadraticMap.PosDef ↔
      ∀ K : M.graph.ConnectedComponent, (M.restrict K.supp).geometricForm.toQuadraticMap.PosDef :=
  M.geometricForm_posDef_iff_of_eq_two _ fun _ _ ↦ M.eq_two_of_connectedComponentMk_ne

end CoxeterMatrix
