/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
-- Proof-only: separation of a point from a closed convex set, reflexivity of finite-dimensional
-- spaces, and compactness of convex hulls.
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Analysis.Convex.Caratheodory

/-!
# Convex hulls of compact families of linear functionals

Let `V` be a finite-dimensional real vector space and let `ν : X → V*` be a family of linear
functionals on `V`, indexed by a topological space `X`, whose evaluations `x ↦ ν x v` are
continuous on a compact set `s ⊆ X`. This file describes the convex hull of `ν '' s` by its
support function: a functional `p` lies in `convexHull ℝ (ν '' s)` exactly when in every
direction `v ∈ V` it is dominated by some member of the family,

`p ∈ convexHull ℝ (ν '' s) ↔ ∀ v, ∃ x ∈ s, p v ≤ ν x v`

(`IsCompact.mem_convexHull_image_iff_forall_exists_apply_le`). No topology on `V` is needed:
compactness enters through the finitely many coordinate evaluations `x ↦ ν x (b i)` for a basis
`b` of `V`, which make the convex hull compact, hence closed, so that a point outside it is
strictly separated from it by a linear functional on `V*`, that is, by evaluation at a vector of
`V`.

When `V` carries a Hausdorff vector space topology, it suffices to test the directions of a dense
set `D ⊆ V` (`IsCompact.mem_convexHull_image_of_dense`): the directions in which `p` is dominated
form a closed set, because `s` is compact. This is the form in which the statement is used for
moment maps of torus actions, where only a dense set of generic directions is directly accessible.

## Main results

* `IsCompact.mem_convexHull_image_iff_forall_exists_apply_le`: a functional lies in the convex hull
  of a compact family of functionals exactly when it is dominated by the family in every
  direction.
* `IsCompact.mem_convexHull_image_of_dense`: for a topological `V`, domination in a dense set of
  directions suffices.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, Theorem 11.5 and
  Corollary 13.1.1 (a closed convex set is determined by its support function).
-/

public section

open Set Module

variable {V X : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace X] {s : Set X} {ν : X → Dual ℝ V} {p : Dual ℝ V}

/-- **Convex hulls of compact families of functionals by support functions.** For a family `ν` of
linear functionals on a finite-dimensional real vector space whose evaluations are continuous on
a compact set `s`, a functional `p` lies in the convex hull of `ν '' s` exactly when for every
vector `v` some `x ∈ s` has `p v ≤ ν x v`. -/
theorem IsCompact.mem_convexHull_image_iff_forall_exists_apply_le (hs : IsCompact s)
    (hν : ∀ v, ContinuousOn (fun x ↦ ν x v) s) :
    p ∈ convexHull ℝ (ν '' s) ↔ ∀ v, ∃ x ∈ s, p v ≤ ν x v := by
  refine ⟨fun hp v ↦ ?_, fun hp ↦ ?_⟩
  · -- Evaluation at `v` is linear, so its maximum on the convex hull is attained on `ν '' s`.
    obtain ⟨_, ⟨x, hx, rfl⟩, hle⟩ :=
      ((Dual.eval ℝ V v).convexOn convex_univ).exists_ge_of_mem_convexHull (subset_univ _) hp
    exact ⟨x, hx, hle⟩
  -- Transport to coordinates `f ↦ (f (b i))ᵢ` for a basis `b` of `V`, where the convex hull of
  -- the compact set `e '' (ν '' s)` is compact, hence an intersection of half-spaces.
  let b := finBasis ℝ V
  let e := b.dualBasis.equivFun
  have hK : IsCompact (e '' (ν '' s)) := by
    rw [image_image]
    exact hs.image_of_continuousOn
      (continuousOn_pi.2 fun i ↦ by simpa only [e, b.dualBasis_equivFun] using hν (b i))
  have himg : e '' _root_.convexHull ℝ (ν '' s) = _root_.convexHull ℝ (e '' (ν '' s)) :=
    e.toLinearMap.image_convexHull _
  rw [← e.injective.mem_set_image, himg,
    ← iInter_halfSpaces_eq (convex_convexHull ℝ _) hK.convexHull.isClosed, mem_iInter]
  intro l
  -- The functional `l ∘ e` on `V*` is evaluation at a vector of `V`, by reflexivity.
  obtain ⟨x, hx, hle⟩ := hp ((evalEquiv ℝ V).symm (l.toLinearMap ∘ₗ e.toLinearMap))
  refine ⟨e (ν x), subset_convexHull ℝ _ (mem_image_of_mem e (mem_image_of_mem ν hx)), ?_⟩
  simpa only [apply_evalEquiv_symm_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe] using hle

/-- **Domination in a dense set of directions.** If `V` is a finite-dimensional Hausdorff real
topological vector space, `ν` a family of linear functionals on `V` with evaluations continuous
on a compact set `s`, and `p` a functional such that for every `v` in a dense set `D ⊆ V` some
`x ∈ s` has `p v ≤ ν x v`, then `p` lies in the convex hull of `ν '' s`. -/
theorem IsCompact.mem_convexHull_image_of_dense [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] [T2Space V] (hs : IsCompact s)
    (hν : ∀ v, ContinuousOn (fun x ↦ ν x v) s) {D : Set V} (hD : Dense D)
    (hp : ∀ v ∈ D, ∃ x ∈ s, p v ≤ ν x v) : p ∈ convexHull ℝ (ν '' s) := by
  refine (hs.mem_convexHull_image_iff_forall_exists_apply_le hν).2 fun v ↦ ?_
  have : CompactSpace s := isCompact_iff_compactSpace.1 hs
  -- In a basis `b` of `V`, `ν x w = ∑ i, b.repr w i * ν x (b i)` is jointly continuous in
  -- `(w, x)`.
  let b := finBasis ℝ V
  have hcont : Continuous fun q : V × s ↦ ν q.2 q.1 := by
    have hsum (q : V × s) : ν q.2 q.1 = ∑ i, b.coord i q.1 * ν q.2 (b i) := calc
      ν q.2 q.1 = ν q.2 (∑ i, b.repr q.1 i • b i) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, Basis.coord_apply]
    simp_rw [hsum]
    exact continuous_finsetSum _ fun i _ ↦
      ((LinearMap.continuous_of_finiteDimensional _).comp continuous_fst).mul
        ((continuousOn_iff_continuous_domRestrict.1 (hν (b i))).comp continuous_snd)
  -- The directions in which `p` is dominated are the projection of a closed subset of `V × s`,
  -- hence closed since `s` is compact.
  have hcl : IsClosed {w : V | ∃ x ∈ s, p w ≤ ν x w} := by
    convert isClosedMap_fst_of_compactSpace _
      (isClosed_le ((LinearMap.continuous_of_finiteDimensional p).comp continuous_fst) hcont)
      using 1
    ext w
    simp
  exact closure_minimal (fun w hw ↦ hp w hw) hcl (hD.closure_eq ▸ mem_univ v)
