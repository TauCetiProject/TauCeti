/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.ConvexSpace.Cube
public import TauCeti.Geometry.Convex.ConvexSpace.Topology

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

/-- A map out of a simplex which sends every facet to `x` sends every point with a vanishing
barycentric coordinate to `x`. -/
private lemma apply_eq_of_weights_eq_zero {n : ℕ} {φ : C(StdSimplex ℝ (Fin (n + 1)), X)}
    (hφ : ∀ (i : Fin (n + 1)) (z : StdSimplex ℝ (Fin n)), φ (z.map i.succAbove) = x)
    {b : StdSimplex ℝ (Fin (n + 1))} {k : Fin (n + 1)} (hb : b.weights k = 0) : φ b = x := by
  obtain ⟨z, rfl⟩ := (StdSimplex.mem_range_map_succAbove_iff k b).2 hb
  exact hφ k z

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
    exact apply_eq_of_weights_eq_zero hφ hk⟩

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

/-- The facets of `Δⁿ⁺¹` other than `0` and `1` are those opposite the vertices `k + 2`. -/
private lemma exists_eq_succ_succ {n : ℕ} {j : Fin (n + 2)} (hj : 1 < j) :
    ∃ k : Fin n, j = k.succ.succ := by
  cases j using Fin.cases with
  | zero => exact absurd hj (by simp)
  | succ j =>
    cases j using Fin.cases with
    | zero => exact absurd hj (by simp)
    | succ k => exact ⟨k, rfl⟩

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
  · obtain ⟨k, rfl⟩ := exists_eq_succ_succ hj
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
    rw [← hz, h0, apply_eq_of_weights_eq_zero hφ hz1]
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

end GenLoop
