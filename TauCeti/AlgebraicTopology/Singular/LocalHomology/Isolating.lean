/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.Homotopy.Affine
import TauCeti.Topology.Compactness.Compact

/-!
# The local degree on an isolating open set

Let `M` and `N` be topological manifolds of the same dimension `n`, oriented by `o` and `o'`
(`TauCeti.HomologicalOrientation`), let `f : M → N` be continuous and let `U ⊆ M` be an open set.
Restricting `f` to `U`, with the orientation `o` restricted to `U`
(`TauCeti.HomologicalOrientation.comap`), gives the local degree of `f` on `U` at `y ∈ N`:

`(o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) y`.

It counts, with orientation signs and multiplicities, the solutions in `U` of `f x = y`. This file
develops the properties of this count under the hypothesis that `U` is *isolating*: the closure of
`U` is compact and `f` does not take the value `y` on the frontier of `U`. Then the solutions of
`f x = y` in `U` form a compact set, as do those of a homotopy which avoids `y` on the frontier
(`TauCeti.isCompact_setOf_apply_eq_of_frontier`), and the count is stable:

* **Homotopy invariance.** The count is unchanged along a homotopy which takes no value `y` on the
  frontier of `U` at any time
  (`TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_homotopy`), and in particular along a
  continuous family of maps over a path in a parameter space on which the frontier stays free of
  solutions (`TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_joinedIn`). The solutions
  may move, appear and disappear in `U`, provided none crosses the frontier.
* **Boundary-bounded perturbations (Rouché's principle).** When `N` is a finite-dimensional real
  normed space, two maps `f` and `g` with `‖g x - f x‖ < ‖f x - y‖ + ‖g x - y‖` on the frontier of
  `U` have the same count (`TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_norm_sub_lt`).
  Since the frontier is compact, an isolating `U` has a positive boundary margin `b ≤ ‖f x - y‖`,
  and every perturbation smaller than `b` on the frontier has the same count
  (`TauCeti.HomologicalOrientation.exists_pos_forall_localDegree_restrict_eq`).
* **Existence.** A nonzero count forces a solution in `U`
  (`TauCeti.HomologicalOrientation.exists_mem_apply_eq_of_localDegree_restrict_ne_zero`).
* **Excision and localization.** The count does not change when `U` is shrunk to an open subset
  containing every solution in `U`
  (`TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_le`); when every solution lies in
  `U` it is the local degree of `f` itself
  (`TauCeti.HomologicalOrientation.localDegree_restrict_eq_localDegree`). When the solutions in `U`
  are finitely many, it is the sum of the local indices of `f` at them
  (`TauCeti.HomologicalOrientation.localDegree_restrict_eq_sum_localIndex`). For a map between open
  subsets of a vector space, the local index at a solution where the derivative is invertible is
  the sign of the Jacobian (`TauCeti.HomologicalOrientation.localIndex_comap_eq_sign_det`), so the
  count is then `∑ sign det Df(x)`.

This is the form in which the solutions of finite-dimensional reductions of nonlinear elliptic
equations are counted (Taubes): a positive boundary margin `b` on an isolating open set lets any
perturbation with sup-norm below `b` on the frontier preserve the oriented count of solutions.

## Main results

* `TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_homotopy`: homotopy invariance on an
  isolating open set.
* `TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_joinedIn`: invariance along a path of
  parameters keeping the frontier free of solutions.
* `TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_norm_sub_lt`: Rouché's principle for
  maps to a normed space.
* `TauCeti.HomologicalOrientation.exists_pos_forall_localDegree_restrict_eq`: an isolating open set
  has a positive boundary margin below which perturbations do not change the count.
* `TauCeti.HomologicalOrientation.exists_mem_apply_eq_of_localDegree_restrict_ne_zero`: a nonzero
  count has a solution.
* `TauCeti.HomologicalOrientation.localDegree_restrict_eq_of_le`,
  `TauCeti.HomologicalOrientation.localDegree_restrict_eq_localDegree`: excision.
* `TauCeti.HomologicalOrientation.localDegree_restrict_eq_sum_localIndex`: the count as a sum of
  local indices.

## References

* K. Deimling, *Nonlinear Functional Analysis*, Springer, 1985, Chapter 1, Theorem 3.1 (the
  properties of the degree on bounded open sets).
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334 (the count of solutions of a finite-dimensional
  reduction on an isolating set).
-/

public section

noncomputable section

open Module Set Topology TopologicalSpace unitInterval

namespace TauCeti

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n)

section Manifold

variable {N F : Type} [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
  (o' : HomologicalOrientation N F n) (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)

include hF in
/-- **Homotopy invariance on an isolating open set.** Let `U` have compact closure, and let `H` be
a homotopy from `f₀` to `f₁` which takes no value `y` on the frontier of `U`. Then `f₀` and `f₁`
have the same local degree on `U` at `y`. -/
theorem localDegree_restrict_eq_of_homotopy {U : Opens M} (hU : IsCompact (closure (U : Set M)))
    {f₀ f₁ : C(M, N)} (H : f₀.Homotopy f₁) {y : N}
    (hH : ∀ t, ∀ x ∈ frontier (U : Set M), H (t, x) ≠ y) :
    (o.comap U.isOpenEmbedding').localDegree o' hE (f₀.restrict U) y =
      (o.comap U.isOpenEmbedding').localDegree o' hE (f₁.restrict U) y := by
  -- The restricted homotopy is `H` read on `I × U`; its solutions form a compact set, being those
  -- of `H` on the compact set `I × closure U`, which avoid the frontier.
  let H' : (f₀.restrict U).Homotopy (f₁.restrict U) :=
    (H.compContinuousMap ⟨Subtype.val, continuous_subtypeVal⟩).cast
      (by ext x; exact (f₀.restrict_apply U x).symm) (by ext x; exact (f₁.restrict_apply U x).symm)
  refine (o.comap U.isOpenEmbedding').localDegree_eq_of_homotopy_of_isCompact o' hE hF H' ?_
  convert isCompact_setOf_apply_eq_of_frontier hU H.continuous hH using 1
  ext ⟨t, x⟩
  simp [H']

include hF in
/-- **Invariance along a path of parameters.** Let `Φ` be a continuous family of maps `M → N`
parametrized by `P`, and let `S ⊆ P` be a set of parameters for which no map of the family takes
the value `y` on the frontier of `U`, where `U` has compact closure. Then any two parameters joined
by a path in `S` give the same local degree on `U` at `y`. -/
theorem localDegree_restrict_eq_of_joinedIn {P : Type*} [TopologicalSpace P] {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) (Φ : C(P × M, N)) {S : Set P} {y : N}
    (hΦ : ∀ p ∈ S, ∀ x ∈ frontier (U : Set M), Φ (p, x) ≠ y) {p q : P} (hpq : JoinedIn S p q) :
    (o.comap U.isOpenEmbedding').localDegree o' hE ((Φ.curry p).restrict U) y =
      (o.comap U.isOpenEmbedding').localDegree o' hE ((Φ.curry q).restrict U) y := by
  let γ := hpq.somePath
  let H : (Φ.curry p).Homotopy (Φ.curry q) :=
    { toFun := fun tx ↦ Φ (γ tx.1, tx.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ by simp
      map_one_left := fun x ↦ by simp }
  exact o.localDegree_restrict_eq_of_homotopy o' hE hF hU H fun t x hx ↦
    hΦ (γ t) (hpq.somePath_mem t) x hx

include hF in
/-- **A nonzero local degree on `U` has a solution in `U`.** -/
theorem exists_mem_apply_eq_of_localDegree_restrict_ne_zero {U : Opens M} {f : C(M, N)} {y : N}
    (h : (o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) y ≠ 0) :
    ∃ x ∈ U, f x = y := by
  obtain ⟨x, hx⟩ := (o.comap U.isOpenEmbedding').mem_range_of_localDegree_ne_zero o' hE hF h
  exact ⟨x, x.property, hx⟩

include hF in
/-- **Excision.** When every solution of `f x = y` lies in `U`, the local degree of `f` on `U` at
`y` is the local degree of `f`. -/
theorem localDegree_restrict_eq_localDegree {U : Opens M} {f : C(M, N)} {y : N}
    (h : f ⁻¹' {y} ⊆ U) :
    (o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) y =
      o.localDegree o' hE f y :=
  o.localDegree_comap_comp o' hE hF (j := ⟨Subtype.val, continuous_subtypeVal⟩)
    U.isOpenEmbedding' f (by simpa using h)

include hF in
/-- **Excision within `U`.** Shrinking `U` to an open subset `V` which contains every solution of
`f x = y` in `U` does not change the local degree. -/
theorem localDegree_restrict_eq_of_le {U V : Opens M} (hVU : V ≤ U) {f : C(M, N)} {y : N}
    (h : f ⁻¹' {y} ∩ U ⊆ V) :
    (o.comap V.isOpenEmbedding').localDegree o' hE (f.restrict V) y =
      (o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) y := by
  -- Read `V` inside `U` through the inclusion, an open embedding.
  let ι : C(V, U) := ContinuousMap.inclusion hVU
  have hι : IsOpenEmbedding ι := Opens.isOpenEmbedding_of_le hVU
  -- A solution `z` of `f.restrict U z = y` is a solution `f z = y` in `U`, by definition of
  -- `ContinuousMap.restrict`.
  have hy : f.restrict U ⁻¹' {y} ⊆ range ι := fun z hz ↦
    ⟨⟨z, h ⟨hz, z.property⟩⟩, rfl⟩
  have key := (o.comap U.isOpenEmbedding').localDegree_comap_comp o' hE hF hι (f.restrict U) hy
  rwa [comap_comap_of_comp_eq _ _ hι V.isOpenEmbedding' rfl] at key

include hF in
/-- **The local degree on `U` as a sum of local indices.** If `f x = y` has finitely many solutions
in `U`, the local degree of `f` on `U` at `y` is the sum of the local indices of `f` at these
solutions. -/
theorem localDegree_restrict_eq_sum_localIndex {U : Opens M} {f : C(M, N)} {y : N}
    (hy : (f ⁻¹' {y} ∩ U).Finite) :
    (o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) y =
      ∑ x ∈ hy.toFinset, o.localIndex o' f x := by
  have hpre : f.restrict U ⁻¹' {y} = Subtype.val ⁻¹' (f ⁻¹' {y} ∩ U) := by
    ext x
    simp only [mem_preimage, mem_inter_iff, ContinuousMap.restrict_apply]
    exact ⟨fun h ↦ ⟨h, x.property⟩, fun h ↦ h.1⟩
  have hy' : (f.restrict U ⁻¹' {y}).Finite :=
    hpre ▸ hy.preimage Subtype.val_injective.injOn
  -- The solutions in `U` are those of the restriction, read in `M`.
  have hfin : hy.toFinset = hy'.toFinset.map (Function.Embedding.subtype _) := by
    ext x
    simp only [Finite.mem_toFinset, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨hx, hxU⟩
      exact ⟨⟨x, hxU⟩, hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.property⟩
  rw [(o.comap U.isOpenEmbedding').localDegree_eq_sum_localIndex o' hE hF _ hy', hfin,
    Finset.sum_map]
  -- Each local index of the restriction is that of `f`, by naturality under open embeddings.
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have h := o.localIndex_comap o' hF U.isOpenEmbedding' IsOpenEmbedding.id
    (f := (f.restrict U : C(U, N))) (g := f) (x := x) (.of_forall fun _ ↦ rfl)
  rwa [comap_id] at h

end Manifold

section Normed

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (o' : HomologicalOrientation F F n) (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)

include hF in
/-- **Rouché's principle.** Let `U` have compact closure, and let `f, g : M → F` satisfy
`‖g x - f x‖ < ‖f x - y‖ + ‖g x - y‖` on the frontier of `U`. Then `f` and `g` have the same local
degree on `U` at `y`: the straight-line homotopy from `f` to `g` takes no value `y` on the
frontier. -/
theorem localDegree_restrict_eq_of_norm_sub_lt {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) {f g : C(M, F)} {y : F}
    (hfg : ∀ x ∈ frontier (U : Set M), ‖g x - f x‖ < ‖f x - y‖ + ‖g x - y‖) :
    (o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) y =
      (o.comap U.isOpenEmbedding').localDegree o' hE (g.restrict U) y := by
  refine o.localDegree_restrict_eq_of_homotopy o' hE hF hU (.affine f g) fun t x hx hxy ↦ ?_
  -- A solution `y` lies on the segment from `f x` to `g x`, so its distances to the endpoints
  -- add up to only `‖g x - f x‖`.
  simp only [ContinuousMap.Homotopy.affine_apply] at hxy
  have hle := (show Wbtw ℝ (f x) y (g x) from ⟨t, t.property, hxy⟩).dist_add_dist
  rw [dist_comm y, dist_comm (f x) (g x), dist_eq_norm, dist_eq_norm, dist_eq_norm] at hle
  exact (hfg x hx).ne' hle

include hF in
/-- **The boundary margin of an isolating open set.** Let `U` have compact closure and let `f` take
no value `y` on the frontier of `U`. Then there is a margin `b > 0` with `b ≤ ‖f x - y‖` on the
frontier, and every map `g` with `‖g x - f x‖ < b` on the frontier has the same local degree on
`U` at `y` as `f`. -/
theorem exists_pos_forall_localDegree_restrict_eq {U : Opens M}
    (hU : IsCompact (closure (U : Set M))) {f : C(M, F)} {y : F}
    (hf : ∀ x ∈ frontier (U : Set M), f x ≠ y) :
    ∃ b > 0, (∀ x ∈ frontier (U : Set M), b ≤ ‖f x - y‖) ∧
      ∀ g : C(M, F), (∀ x ∈ frontier (U : Set M), ‖g x - f x‖ < b) →
        (o.comap U.isOpenEmbedding').localDegree o' hE (g.restrict U) y =
          (o.comap U.isOpenEmbedding').localDegree o' hE (f.restrict U) y := by
  have hfr : IsCompact (frontier (U : Set M)) :=
    hU.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨b, hb, hbf⟩ := hfr.exists_forall_le' (f := fun x ↦ ‖f x - y‖) (by fun_prop)
    fun x hx ↦ norm_pos_iff.2 (sub_ne_zero.2 (hf x hx))
  exact ⟨b, hb, hbf, fun g hg ↦ (o.localDegree_restrict_eq_of_norm_sub_lt o' hE hF hU
    fun x hx ↦ lt_add_of_lt_of_nonneg ((hg x hx).trans_le (hbf x hx)) (norm_nonneg _)).symm⟩

end Normed

end HomologicalOrientation

end TauCeti
