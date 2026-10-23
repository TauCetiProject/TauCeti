/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.ConvexSpace.Cube
public import TauCeti.Geometry.Convex.ConvexSpace.Topology

import TauCeti.Data.Fin.Basic
import TauCeti.Topology.Homotopy.HomotopyGroup.TransAt

/-!
# Generalized loops as maps out of a simplex

Mathlib's homotopy groups `HomotopyGroup (Fin n) X x` are built from generalized loops
`Ω^ (Fin n) X x`, the maps `Iⁿ → X` sending the boundary of the cube to `x`. This file describes
them, and their homotopies relative to the boundary, by maps out of standard simplices, which is
the form in which homotopy groups of the singular simplicial set of `X` are defined.

The map `Convexity.StdSimplex.ofCube n : Iⁿ → Δⁿ` is a continuous surjection from a compact space
onto a Hausdorff space, hence a quotient map, and it only identifies points of the boundary of
the cube, which it sends to the boundary of the simplex. So precomposition with it is a
bijection from the maps `Δⁿ → X` sending every facet to `x` onto the generalized loops
(`GenLoop.simplexEquiv`).

Similarly, `(s, t) ↦ prism s (ofCube n t)` is a quotient map `I × Iⁿ → Δⁿ⁺¹` whose ends are the
facets `0` and `1` of `Δⁿ⁺¹`, and which sends `I × ∂Iⁿ` to the union of the other facets and of
the boundaries of the facets `0` and `1`. Hence two generalized loops coming from maps
`φ, ψ : Δⁿ → X` are homotopic relative to the boundary exactly when there is a map
`τ : Δⁿ⁺¹ → X` whose facets `0` and `1` are `φ` and `ψ` and whose other facets are sent to `x`
(`GenLoop.homotopic_simplexEquiv_iff`). This is the topological counterpart of the combinatorial
homotopy relation `SSet.PtSimplex.RelStruct₀` on pointed simplices.

Products are described in the same way. Let `τ : Δⁿ⁺² → X` send its facets `j < n` to `x`, with
facets `n`, `n + 1` and `n + 2` sending their boundaries to `x`. The last coordinate of the cube
`Iⁿ⁺¹` runs along an edge of the triangle spanned by the last three vertices of `Δⁿ⁺²`, coned off
over the first `n` coordinates (`Convexity.StdSimplex.splitLast_ofCube_init`). A straight-line
homotopy in that triangle, from the edge `n → n + 2` to the edges `n → n + 1 → n + 2`, shows that
the generalized loop of the facet `n + 1` is homotopic to the concatenation, along the last
direction, of the generalized loops of the facets `n + 2` and `n`
(`GenLoop.homotopic_simplexEquiv_transAt_last`). This is the topological counterpart of
`SSet.PtSimplex.MulStruct`, which defines products in homotopy groups of Kan complexes.

## References

* J. P. May, *Simplicial Objects in Algebraic Topology*, University of Chicago Press, 1967,
  §16, for the comparison of simplicial and topological homotopy groups.
-/

public noncomputable section

open unitInterval Convexity
open Topology
open scoped Topology.Homotopy

namespace GenLoop

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- `Convexity.StdSimplex.ofCube n` as a continuous map. -/
private def ofCubeMap (n : ℕ) : C(I^(Fin n), StdSimplex ℝ (Fin (n + 1))) :=
  ⟨StdSimplex.ofCube n, StdSimplex.continuous_ofCube n⟩

private lemma isQuotientMap_ofCubeMap (n : ℕ) : IsQuotientMap (ofCubeMap n) :=
  .of_surjective_continuous (StdSimplex.surjective_ofCube n) (StdSimplex.continuous_ofCube n)

/-- A generalized loop is constant on the fibres of `ofCube n`, which are points or lie in
`∂Iⁿ`. -/
private lemma factorsThrough_ofCubeMap {n : ℕ} (g : Ω^ (Fin n) X x) :
    Function.FactorsThrough g.1 (ofCubeMap n) := fun t t' h => by
  rcases StdSimplex.eq_or_mem_boundary_of_ofCube_eq h with rfl | ⟨ht, ht'⟩
  · rfl
  · exact (g.2 t ht).trans (g.2 t' ht').symm

/-- The generalized loop `φ ∘ ofCube n` of a map `φ : Δⁿ → X` sending every facet to `x`. -/
private def toGenLoop {n : ℕ} {φ : C(StdSimplex ℝ (Fin (n + 1)), X)}
    (hφ : ∀ (i : Fin (n + 1)) (z : StdSimplex ℝ (Fin n)), φ (z.map i.succAbove) = x) :
    Ω^ (Fin n) X x :=
  ⟨φ.comp (ofCubeMap n), fun t ht => by
    obtain ⟨k, hk⟩ := StdSimplex.exists_weights_ofCube_eq_zero_iff.2 ht
    exact StdSimplex.apply_eq_of_weights_eq_zero hφ hk⟩

/-- The map `Δⁿ → X` through which a generalized loop factors along the quotient map
`ofCube n`. -/
private def ofGenLoop {n : ℕ} (g : Ω^ (Fin n) X x) :
    {φ : C(StdSimplex ℝ (Fin (n + 1)), X) //
      ∀ (i : Fin (n + 1)) (z : StdSimplex ℝ (Fin n)), φ (z.map i.succAbove) = x} :=
  ⟨(isQuotientMap_ofCubeMap n).lift g.1 (factorsThrough_ofCubeMap g), fun i z => by
    obtain ⟨t, ht⟩ := StdSimplex.surjective_ofCube n (z.map i.succAbove)
    have hb := StdSimplex.weights_map_succAbove_self (R := ℝ) i z
    rw [← ht] at hb ⊢
    exact (DFunLike.congr_fun ((isQuotientMap_ofCubeMap n).lift_comp g.1
      (factorsThrough_ofCubeMap g)) t).trans
      (g.2 t (StdSimplex.mem_boundary_of_weights_ofCube_eq_zero hb))⟩

variable (X x) in
/-- The generalized loops `Iⁿ → X` at `x` are the maps `Δⁿ → X` sending every facet to `x`,
through precomposition with the quotient map `Convexity.StdSimplex.ofCube n : Iⁿ → Δⁿ`. -/
def simplexEquiv (n : ℕ) :
    {φ : C(StdSimplex ℝ (Fin (n + 1)), X) //
      ∀ (i : Fin (n + 1)) (z : StdSimplex ℝ (Fin n)), φ (z.map i.succAbove) = x} ≃
      Ω^ (Fin n) X x where
  toFun φ := toGenLoop φ.2
  invFun := ofGenLoop
  left_inv φ := by
    refine Subtype.ext (ContinuousMap.ext fun b => ?_)
    obtain ⟨t, rfl⟩ := StdSimplex.surjective_ofCube n b
    exact DFunLike.congr_fun ((isQuotientMap_ofCubeMap n).lift_comp _
      (factorsThrough_ofCubeMap (toGenLoop φ.2))) t
  right_inv g := GenLoop.ext _ _ fun t =>
    DFunLike.congr_fun ((isQuotientMap_ofCubeMap n).lift_comp g.1 (factorsThrough_ofCubeMap g)) t

@[simp]
lemma simplexEquiv_apply {n : ℕ}
    (φ : {φ : C(StdSimplex ℝ (Fin (n + 1)), X) //
      ∀ (i : Fin (n + 1)) (z : StdSimplex ℝ (Fin n)), φ (z.map i.succAbove) = x})
    (t : I^(Fin n)) :
    simplexEquiv X x n φ t = φ.1 (StdSimplex.ofCube n t) :=
  (rfl)

@[simp]
lemma simplexEquiv_symm_apply_ofCube {n : ℕ} (g : Ω^ (Fin n) X x) (t : I^(Fin n)) :
    ((simplexEquiv X x n).symm g).1 (StdSimplex.ofCube n t) = g t :=
  DFunLike.congr_fun ((isQuotientMap_ofCubeMap n).lift_comp g.1 (factorsThrough_ofCubeMap g)) t

/-- The map `I × Iⁿ → Δⁿ⁺¹`, `(s, t) ↦ prism s (ofCube n t)`. -/
private def prismOfCubeMap (n : ℕ) : C(I × I^(Fin n), StdSimplex ℝ (Fin (n + 2))) :=
  ⟨fun p => StdSimplex.prism p.1 (StdSimplex.ofCube n p.2), by fun_prop⟩

private lemma prismOfCubeMap_apply (n : ℕ) (p : I × I^(Fin n)) :
    prismOfCubeMap n p = StdSimplex.prism p.1 (StdSimplex.ofCube n p.2) :=
  (rfl)

private lemma isQuotientMap_prismOfCubeMap (n : ℕ) : IsQuotientMap (prismOfCubeMap n) := by
  refine .of_surjective_continuous (fun v => ?_) (prismOfCubeMap n).continuous
  obtain ⟨⟨s, w⟩, rfl⟩ := StdSimplex.surjective_prism v
  obtain ⟨t, rfl⟩ := StdSimplex.surjective_ofCube n w
  exact ⟨(s, t), rfl⟩

/-- A homotopy relative to the boundary between the generalized loops of `φ` and `ψ` descends
along the quotient map `I × Iⁿ → Δⁿ⁺¹` to a map with facets `φ`, `ψ` and `x`. -/
private lemma exists_isFacetHomotopy {n : ℕ}
    {φ ψ : {φ : C(StdSimplex ℝ (Fin (n + 1)), X) //
      ∀ (i : Fin (n + 1)) (z : StdSimplex ℝ (Fin n)), φ (z.map i.succAbove) = x}}
    (F : (simplexEquiv X x n φ : C(I^(Fin n), X)).HomotopyRel (simplexEquiv X x n ψ)
      (Cube.boundary (Fin n))) :
    ∃ τ : C(StdSimplex ℝ (Fin (n + 2)), X),
      (∀ z : StdSimplex ℝ (Fin (n + 1)), τ (z.map (0 : Fin (n + 2)).succAbove) = φ.1 z) ∧
      (∀ z : StdSimplex ℝ (Fin (n + 1)), τ (z.map (1 : Fin (n + 2)).succAbove) = ψ.1 z) ∧
      ∀ j : Fin (n + 2), 1 < j → ∀ z : StdSimplex ℝ (Fin (n + 1)), τ (z.map j.succAbove) = x := by
  have hq := isQuotientMap_prismOfCubeMap n
  have hF (s : I) {t : I^(Fin n)} (ht : t ∈ Cube.boundary (Fin n)) : F (s, t) = x :=
    (F.eq_fst s ht).trans ((simplexEquiv X x n φ).2 t ht)
  -- `F` is constant on the fibres of the quotient map, which lie in `I × ∂Iⁿ` unless they are
  -- points.
  have hfac : Function.FactorsThrough F.toContinuousMap (prismOfCubeMap n) := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    obtain ⟨hw, hs⟩ := StdSimplex.prism_eq_prism_iff.1 h
    rcases StdSimplex.eq_or_mem_boundary_of_ofCube_eq hw with rfl | ⟨ht, ht'⟩
    · rcases hs with rfl | h0
      · rfl
      · have ht := StdSimplex.mem_boundary_of_weights_ofCube_eq_zero h0
        exact (hF s ht).trans (hF s' ht).symm
    · exact (hF s ht).trans (hF s' ht').symm
  have hτ (s : I) (t : I^(Fin n)) :
      hq.lift F.toContinuousMap hfac (StdSimplex.prism s (StdSimplex.ofCube n t)) = F (s, t) :=
    DFunLike.congr_fun (hq.lift_comp F.toContinuousMap hfac) (s, t)
  refine ⟨hq.lift F.toContinuousMap hfac, fun z => ?_, fun z => ?_, fun j hj z => ?_⟩
  · obtain ⟨t, rfl⟩ := StdSimplex.surjective_ofCube n z
    rw [← StdSimplex.prism_zero, hτ, F.apply_zero]
    rfl
  · obtain ⟨t, rfl⟩ := StdSimplex.surjective_ofCube n z
    rw [← StdSimplex.prism_one, hτ, F.apply_one]
    rfl
  · obtain ⟨k, rfl⟩ := Fin.exists_succ_succ_eq.2 hj
    obtain ⟨⟨s, t⟩, hst⟩ := hq.surjective (z.map k.succ.succ.succAbove)
    have hb := StdSimplex.weights_map_succAbove_self (R := ℝ) k.succ.succ z
    rw [← hst, prismOfCubeMap_apply, StdSimplex.prism_weights_succ_succ] at hb
    rw [← hst, prismOfCubeMap_apply, hτ]
    exact hF s (StdSimplex.mem_boundary_of_weights_ofCube_eq_zero hb)

/-- A map `τ : Δⁿ⁺¹ → X` whose facet `0` sends its boundary to `x` and whose facets other than
`0` and `1` are sent to `x` sends `prism s (ofCube n t)` to `x` for `t` on the boundary of the
cube: such a point lies in a facet `k + 2` of `Δⁿ⁺¹`, or in the boundary of its facet `0`. -/
private lemma apply_prism_ofCube_of_mem_boundary {n : ℕ} {φ : C(StdSimplex ℝ (Fin (n + 1)), X)}
    (hφ : ∀ (i : Fin (n + 1)) (z : StdSimplex ℝ (Fin n)), φ (z.map i.succAbove) = x)
    {τ : C(StdSimplex ℝ (Fin (n + 2)), X)}
    (h0 : ∀ z : StdSimplex ℝ (Fin (n + 1)), τ (z.map (0 : Fin (n + 2)).succAbove) = φ z)
    (hj : ∀ j : Fin (n + 2), 1 < j → ∀ z : StdSimplex ℝ (Fin (n + 1)),
      τ (z.map j.succAbove) = x)
    (s : I) {t : I^(Fin n)} (ht : t ∈ Cube.boundary (Fin n)) :
    τ (StdSimplex.prism s (StdSimplex.ofCube n t)) = x := by
  obtain ⟨k, hk⟩ := StdSimplex.exists_weights_ofCube_eq_zero_iff.2 ht
  cases k using Fin.cases with
  | zero =>
    obtain ⟨z, hz⟩ := (StdSimplex.mem_range_map_succAbove_iff 0
      (StdSimplex.prism s (StdSimplex.ofCube n t))).2 (by simp [hk])
    have hz1 : z.weights 0 = 0 := by
      have := congrArg (fun v => v.weights (Fin.succ 0)) hz
      simp only [Fin.succAbove_zero,
        StdSimplex.weights_map_apply_of_injective (Fin.succ_injective _)] at this
      rwa [Fin.succ_zero_eq_one', StdSimplex.prism_weights_one, hk, mul_zero] at this
    rw [← hz, h0, StdSimplex.apply_eq_of_weights_eq_zero hφ hz1]
  | succ k =>
    obtain ⟨z, hz⟩ := (StdSimplex.mem_range_map_succAbove_iff k.succ.succ
      (StdSimplex.prism s (StdSimplex.ofCube n t))).2 (by simp [hk])
    exact hz ▸ hj k.succ.succ (by simp [Fin.lt_def]) z

/-- Two generalized loops coming from maps `φ, ψ : Δⁿ → X` are homotopic relative to the
boundary exactly when `φ` and `ψ` are the facets `0` and `1` of a map `τ : Δⁿ⁺¹ → X` sending its
other facets to `x`. -/
theorem homotopic_simplexEquiv_iff {n : ℕ}
    {φ ψ : {φ : C(StdSimplex ℝ (Fin (n + 1)), X) //
      ∀ (i : Fin (n + 1)) (z : StdSimplex ℝ (Fin n)), φ (z.map i.succAbove) = x}} :
    GenLoop.Homotopic (simplexEquiv X x n φ) (simplexEquiv X x n ψ) ↔
      ∃ τ : C(StdSimplex ℝ (Fin (n + 2)), X),
        (∀ z : StdSimplex ℝ (Fin (n + 1)), τ (z.map (0 : Fin (n + 2)).succAbove) = φ.1 z) ∧
        (∀ z : StdSimplex ℝ (Fin (n + 1)), τ (z.map (1 : Fin (n + 2)).succAbove) = ψ.1 z) ∧
        ∀ j : Fin (n + 2), 1 < j → ∀ z : StdSimplex ℝ (Fin (n + 1)),
          τ (z.map j.succAbove) = x := by
  refine ⟨fun ⟨F⟩ => exists_isFacetHomotopy F, fun ⟨τ, h0, h1, hj⟩ => ?_⟩
  -- The homotopy is `τ` composed with the quotient map `I × Iⁿ → Δⁿ⁺¹`.
  refine ⟨{ toFun := fun p => τ (StdSimplex.prism p.1 (StdSimplex.ofCube n p.2))
            continuous_toFun := by fun_prop
            map_zero_left := fun t => (congrArg τ (StdSimplex.prism_zero _)).trans (h0 _)
            map_one_left := fun t => (congrArg τ (StdSimplex.prism_one _)).trans (h1 _)
            prop' := fun s t ht => ?_ }⟩
  have hx : (simplexEquiv X x n φ : C(I^(Fin n), X)) t = x := (simplexEquiv X x n φ).2 t ht
  simp only [ContinuousMap.coe_mk, hx]
  exact apply_prism_ofCube_of_mem_boundary φ.2 h0 hj s ht

/-! ### Concatenation along the last direction -/

/-- The straight-line homotopy in the triangle `Δ²` from the edge path `0 → 2` to the
concatenation of the edge paths `0 → 1` and `1 → 2`: at time `u` and parameter `s` its barycentric
coordinates are `(1 - u) (1 - s, 0, s) + u (max (1 - 2s) 0, min (2s) (2 - 2s), max (2s - 1) 0)`. -/
private def triangleHomotopy (u s : I) : StdSimplex ℝ (Fin 3) where
  weights := Finsupp.equivFunOnFinite.symm
    ![(1 - u) * (1 - s) + u * max (1 - 2 * (s : ℝ)) 0, u * min (2 * (s : ℝ)) (2 - 2 * s),
      (1 - u) * s + u * max (2 * (s : ℝ) - 1) 0]
  nonneg k := by
    have hu := sub_nonneg.2 u.2.2
    fin_cases k
    · exact add_nonneg (mul_nonneg hu (sub_nonneg.2 s.2.2)) (mul_nonneg u.2.1 (le_max_right _ _))
    · exact mul_nonneg u.2.1 (le_min (by linarith [s.2.1]) (by linarith [s.2.2]))
    · exact add_nonneg (mul_nonneg hu s.2.1) (mul_nonneg u.2.1 (le_max_right _ _))
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Fin.sum_univ_three]
    rcases le_total (2 * (s : ℝ)) 1 with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), min_eq_left (by linarith)]
      simp
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), min_eq_right (by linarith)]
      simp
      ring

private lemma continuous_triangleHomotopy {Y : Type*} [TopologicalSpace Y] {u s : Y → I}
    (hu : Continuous u) (hs : Continuous s) : Continuous fun y => triangleHomotopy (u y) (s y) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff, continuous_pi_iff]
  intro k
  fin_cases k <;>
    simp only [Function.comp_apply, triangleHomotopy, Finsupp.equivFunOnFinite_symm_apply_apply] <;>
    fun_prop

/-- At time `0`, the homotopy `triangleHomotopy` is the edge path `0 → 2`. -/
private lemma triangleHomotopy_zero (s : I) :
    triangleHomotopy 0 s = (StdSimplex.ofCube 1 fun _ => s).map (1 : Fin 3).succAbove := by
  refine StdSimplex.ext_fin_three ?_ ?_ ?_
  · rw [StdSimplex.weights_map_succAbove_of_eq (i := 0) (by decide)]
    simp [triangleHomotopy]
  · rw [StdSimplex.weights_map_succAbove_self]
    simp [triangleHomotopy]
  · rw [StdSimplex.weights_map_succAbove_of_eq (i := 1) (by decide),
      StdSimplex.ofCube_one_weights_one]
    simp [triangleHomotopy]

/-- At time `1` and on the first half, the homotopy `triangleHomotopy` runs the edge path
`0 → 1` at double speed. -/
private lemma triangleHomotopy_one_of_le {s : I} (h : (s : ℝ) ≤ 1 / 2) {a : I}
    (ha : (a : ℝ) = 2 * s) :
    triangleHomotopy 1 s = (StdSimplex.ofCube 1 fun _ => a).map (2 : Fin 3).succAbove := by
  have h0 : 0 ≤ 1 - 2 * (s : ℝ) := by linarith
  have h1 : 2 * (s : ℝ) ≤ 2 - 2 * s := by linarith
  have h2 : 2 * (s : ℝ) - 1 ≤ 0 := by linarith
  refine StdSimplex.ext_fin_three ?_ ?_ ?_
  · rw [StdSimplex.weights_map_succAbove_of_eq (i := 0) (by decide)]
    simp [triangleHomotopy, ha, max_eq_left h0]
  · rw [StdSimplex.weights_map_succAbove_of_eq (i := 1) (by decide),
      StdSimplex.ofCube_one_weights_one]
    simp [triangleHomotopy, ha, min_eq_left h1]
  · rw [StdSimplex.weights_map_succAbove_self]
    simp [triangleHomotopy, max_eq_right h2]

/-- At time `1` and on the second half, the homotopy `triangleHomotopy` runs the edge path
`1 → 2` at double speed. -/
private lemma triangleHomotopy_one_of_lt {s : I} (h : 1 / 2 < (s : ℝ)) {a : I}
    (ha : (a : ℝ) = 2 * s - 1) :
    triangleHomotopy 1 s = (StdSimplex.ofCube 1 fun _ => a).map (0 : Fin 3).succAbove := by
  have h0 : 1 - 2 * (s : ℝ) ≤ 0 := by linarith
  have h1 : 2 - 2 * (s : ℝ) ≤ 2 * s := by linarith
  have h2 : 0 ≤ 2 * (s : ℝ) - 1 := by linarith
  refine StdSimplex.ext_fin_three ?_ ?_ ?_
  · rw [StdSimplex.weights_map_succAbove_self]
    simp [triangleHomotopy, max_eq_right h0]
  · rw [StdSimplex.weights_map_succAbove_of_eq (i := 0) (by decide)]
    simp [triangleHomotopy, ha, min_eq_right h1]
    ring
  · rw [StdSimplex.weights_map_succAbove_of_eq (i := 1) (by decide),
      StdSimplex.ofCube_one_weights_one]
    simp [triangleHomotopy, ha, max_eq_left h2]

/-- A map `τ : Δⁿ⁺² → X` whose facets `j < n` are sent to `x` and whose facets `n` and `n + 2` send
their boundaries to `x` sends to `x` every point whose weight `n + 1` vanishes together with the
weight `n` or the weight `n + 2`: such a point lies on the boundary of the facet `n` or `n + 2`. -/
private lemma apply_eq_of_weights_natAdd_eq_zero {n : ℕ} {τ : C(StdSimplex ℝ (Fin (n + 3)), X)}
    {φ ψ : {φ : C(StdSimplex ℝ (Fin (n + 2)), X) //
      ∀ (i : Fin (n + 2)) (z : StdSimplex ℝ (Fin (n + 1))), φ (z.map i.succAbove) = x}}
    (hψ : ∀ z, τ (z.map (Fin.natAdd n (0 : Fin 3)).succAbove) = ψ.1 z)
    (hφ : ∀ z, τ (z.map (Fin.natAdd n (2 : Fin 3)).succAbove) = φ.1 z)
    {z : StdSimplex ℝ (Fin (n + 3))} (h1 : z.weights (Fin.natAdd n (1 : Fin 3)) = 0)
    (h : z.weights (Fin.natAdd n (0 : Fin 3)) = 0 ∨ z.weights (Fin.natAdd n (2 : Fin 3)) = 0) :
    τ z = x := by
  rcases h with h | h
  · obtain ⟨w, rfl⟩ := (StdSimplex.mem_range_map_succAbove_iff _ z).2 h
    -- The vertex `n + 1` of `Δⁿ⁺²` is the vertex `n` of its facet `n`.
    have hi : (Fin.natAdd n (0 : Fin 3)).succAbove (Fin.natAdd n (0 : Fin 2)) =
        Fin.natAdd n (1 : Fin 3) := by
      rw [Fin.natAdd_succAbove_natAdd]; rfl
    rw [← hi, StdSimplex.weights_map_apply_of_injective Fin.succAbove_right_injective] at h1
    rw [hψ, StdSimplex.apply_eq_of_weights_eq_zero ψ.2 h1]
  · obtain ⟨w, rfl⟩ := (StdSimplex.mem_range_map_succAbove_iff _ z).2 h
    -- The vertex `n + 1` of `Δⁿ⁺²` is the vertex `n + 1` of its facet `n + 2`.
    have hi : (Fin.natAdd n (2 : Fin 3)).succAbove (Fin.natAdd n (1 : Fin 2)) =
        Fin.natAdd n (1 : Fin 3) := by
      rw [Fin.natAdd_succAbove_natAdd]; rfl
    rw [← hi, StdSimplex.weights_map_apply_of_injective Fin.succAbove_right_injective] at h1
    rw [hφ, StdSimplex.apply_eq_of_weights_eq_zero φ.2 h1]

/-- The map `I × Iⁿ⁺¹ → Δⁿ⁺²` which runs `triangleHomotopy` in the triangle spanned by the last
three vertices, at the parameter given by the last coordinate of the cube: the last vertex of
`ofCube n` of the first `n` coordinates is split into the point of that triangle. -/
private def triangleCubeMap (n : ℕ) (p : I × (I^(Fin (n + 1)))) : StdSimplex ℝ (Fin (n + 3)) :=
  StdSimplex.splitLast (StdSimplex.ofCube n (Fin.init p.2))
    (triangleHomotopy p.1 (p.2 (Fin.last n)))

private lemma continuous_triangleCubeMap (n : ℕ) : Continuous (triangleCubeMap n) :=
  StdSimplex.continuous_splitLast.comp <|
    ((StdSimplex.continuous_ofCube n).comp
      (continuous_pi fun i => (continuous_apply i.castSucc).comp continuous_snd)).prodMk
    (continuous_triangleHomotopy continuous_fst
      ((continuous_apply (Fin.last n)).comp continuous_snd))

/-- At time `0`, `triangleCubeMap` is `ofCube (n + 1)` followed by the face map `n + 1`. -/
private lemma triangleCubeMap_zero {n : ℕ} (t : I^(Fin (n + 1))) :
    triangleCubeMap n (0, t) =
      (StdSimplex.ofCube (n + 1) t).map (Fin.natAdd n (1 : Fin 3)).succAbove := by
  rw [triangleCubeMap, triangleHomotopy_zero, StdSimplex.splitLast_map_succAbove,
    StdSimplex.splitLast_ofCube_init]

/-- At time `1` and on the first half, `triangleCubeMap` is `ofCube (n + 1)` at the point with
doubled last coordinate, followed by the face map `n + 2`. -/
private lemma triangleCubeMap_one_of_le {n : ℕ} {t : I^(Fin (n + 1))}
    (h : (t (Fin.last n) : ℝ) ≤ 1 / 2) {a : I} (ha : (a : ℝ) = 2 * t (Fin.last n)) :
    triangleCubeMap n (1, t) =
      (StdSimplex.ofCube (n + 1) (Function.update t (Fin.last n) a)).map
        (Fin.natAdd n (2 : Fin 3)).succAbove := by
  rw [triangleCubeMap, triangleHomotopy_one_of_le h ha, StdSimplex.splitLast_map_succAbove,
    StdSimplex.splitLast_ofCube_init_ofCube_one]

/-- At time `1` and on the second half, `triangleCubeMap` is `ofCube (n + 1)` at the point with
last coordinate `2 tₙ - 1`, followed by the face map `n`. -/
private lemma triangleCubeMap_one_of_lt {n : ℕ} {t : I^(Fin (n + 1))}
    (h : 1 / 2 < (t (Fin.last n) : ℝ)) {a : I} (ha : (a : ℝ) = 2 * t (Fin.last n) - 1) :
    triangleCubeMap n (1, t) =
      (StdSimplex.ofCube (n + 1) (Function.update t (Fin.last n) a)).map
        (Fin.natAdd n (0 : Fin 3)).succAbove := by
  rw [triangleCubeMap, triangleHomotopy_one_of_lt h ha, StdSimplex.splitLast_map_succAbove,
    StdSimplex.splitLast_ofCube_init_ofCube_one]

/-- Over the boundary of the cube, `triangleCubeMap` lands in a facet `j < n` of `Δⁿ⁺²`, or on the
boundary of its facet `n` or `n + 2`. So a map `τ` sending these to `x` sends it to `x`. -/
private lemma apply_triangleCubeMap_of_mem_boundary {n : ℕ} {τ : C(StdSimplex ℝ (Fin (n + 3)), X)}
    {φ ψ : {φ : C(StdSimplex ℝ (Fin (n + 2)), X) //
      ∀ (i : Fin (n + 2)) (z : StdSimplex ℝ (Fin (n + 1))), φ (z.map i.succAbove) = x}}
    (hlt : ∀ j : Fin (n + 3), j < Fin.natAdd n (0 : Fin 3) →
      ∀ z : StdSimplex ℝ (Fin (n + 2)), τ (z.map j.succAbove) = x)
    (hψ : ∀ z, τ (z.map (Fin.natAdd n (0 : Fin 3)).succAbove) = ψ.1 z)
    (hφ : ∀ z, τ (z.map (Fin.natAdd n (2 : Fin 3)).succAbove) = φ.1 z)
    (u : I) {t : I^(Fin (n + 1))} (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    τ (triangleCubeMap n (u, t)) = x := by
  obtain ⟨i, hi⟩ := ht
  cases i using Fin.lastCases with
  | cast i =>
    -- A coordinate other than the last is `0` or `1`, so a weight of `ofCube n` vanishes.
    obtain ⟨k, hk⟩ := StdSimplex.exists_weights_ofCube_eq_zero_iff.2
      (⟨i, hi⟩ : Fin.init t ∈ Cube.boundary (Fin n))
    cases k using Fin.lastCases with
    | cast k =>
      have hz : (triangleCubeMap n (u, t)).weights (Fin.castAdd 3 k) = 0 := by
        simp [triangleCubeMap, hk]
      obtain ⟨w, hw⟩ := (StdSimplex.mem_range_map_succAbove_iff _ _).2 hz
      rw [← hw]
      exact hlt _ (by simp [Fin.lt_def]) w
    | last =>
      exact apply_eq_of_weights_natAdd_eq_zero hψ hφ (by simp [triangleCubeMap, hk])
        (Or.inl (by simp [triangleCubeMap, hk]))
  | last =>
    -- The last coordinate is `0` or `1`, so `triangleHomotopy` is at a vertex of the triangle.
    rcases hi with hi | hi
    · exact apply_eq_of_weights_natAdd_eq_zero hψ hφ
        (by simp [triangleCubeMap, triangleHomotopy, hi])
        (Or.inr (by simp [triangleCubeMap, triangleHomotopy, hi]))
    · exact apply_eq_of_weights_natAdd_eq_zero hψ hφ
        (by simp [triangleCubeMap, triangleHomotopy, hi])
        (Or.inl (by simp [triangleCubeMap, triangleHomotopy, hi]))

/-- Let `τ : Δⁿ⁺² → X` send its facets `j < n` to `x`, and let its facets `n`, `n + 1` and `n + 2`
be `ψ`, `χ` and `φ`, maps `Δⁿ⁺¹ → X` sending every facet to `x`. Then the generalized loop of `χ`
is homotopic relative to the boundary to the concatenation, along the last direction of the cube,
of the generalized loops of `φ` and `ψ`. This is the topological counterpart of the products
`SSet.PtSimplex.MulStruct` in the last direction. -/
theorem homotopic_simplexEquiv_transAt_last {n : ℕ}
    {φ ψ χ : {φ : C(StdSimplex ℝ (Fin (n + 2)), X) //
      ∀ (i : Fin (n + 2)) (z : StdSimplex ℝ (Fin (n + 1))), φ (z.map i.succAbove) = x}}
    (τ : C(StdSimplex ℝ (Fin (n + 3)), X))
    (hlt : ∀ j : Fin (n + 3), j < (Fin.last n).castSucc.castSucc →
      ∀ z : StdSimplex ℝ (Fin (n + 2)), τ (z.map j.succAbove) = x)
    (hψ : ∀ z : StdSimplex ℝ (Fin (n + 2)),
      τ (z.map (Fin.last n).castSucc.castSucc.succAbove) = ψ.1 z)
    (hχ : ∀ z : StdSimplex ℝ (Fin (n + 2)), τ (z.map (Fin.last n).castSucc.succ.succAbove) = χ.1 z)
    (hφ : ∀ z : StdSimplex ℝ (Fin (n + 2)), τ (z.map (Fin.last n).succ.succ.succAbove) = φ.1 z) :
    GenLoop.Homotopic (simplexEquiv X x (n + 1) χ)
      (transAt (Fin.last n) (simplexEquiv X x (n + 1) φ) (simplexEquiv X x (n + 1) ψ)) := by
  -- The facets `n`, `n + 1` and `n + 2` of `Δⁿ⁺²` are those opposite the vertices of its last
  -- triangle.
  have h0 : (Fin.last n).castSucc.castSucc = Fin.natAdd n (0 : Fin 3) := Fin.ext rfl
  have h1 : (Fin.last n).castSucc.succ = Fin.natAdd n (1 : Fin 3) := Fin.ext rfl
  have h2 : (Fin.last n).succ.succ = Fin.natAdd n (2 : Fin 3) := Fin.ext rfl
  rw [h0] at hlt hψ
  rw [h1] at hχ
  rw [h2] at hφ
  refine ⟨{ toFun := fun p => τ (triangleCubeMap n p)
            continuous_toFun := τ.continuous.comp (continuous_triangleCubeMap n)
            map_zero_left := fun t => (congrArg τ (triangleCubeMap_zero t)).trans (hχ _)
            map_one_left := fun t => ?_
            prop' := fun u t ht => ?_ }⟩
  · have ht := (t (Fin.last n)).2
    by_cases h : (t (Fin.last n) : ℝ) ≤ 1 / 2
    · let a : I := ⟨2 * t (Fin.last n), by linarith [ht.1], by linarith⟩
      refine Eq.trans ?_ (transAt_apply_of_le (Fin.last n) _ _ h (a := a) rfl).symm
      rw [triangleCubeMap_one_of_le h (a := a) rfl, hφ, simplexEquiv_apply]
    · rw [not_le] at h
      let a : I := ⟨2 * t (Fin.last n) - 1, by linarith, by linarith [ht.2]⟩
      refine Eq.trans ?_ (transAt_apply_of_lt (Fin.last n) _ _ h (a := a) rfl).symm
      rw [triangleCubeMap_one_of_lt h (a := a) rfl, hψ, simplexEquiv_apply]
  · rw [ContinuousMap.coe_mk, apply_triangleCubeMap_of_mem_boundary hlt hψ hφ u ht]
    exact ((simplexEquiv X x (n + 1) χ).2 t ht).symm

end GenLoop
