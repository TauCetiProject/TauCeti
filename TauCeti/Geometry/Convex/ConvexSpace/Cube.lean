/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Geometry.Convex.ConvexSpace.Defs

import TauCeti.Data.Fin.Basic

/-!
# Standard simplices as quotients of the cube and the prism

This file constructs two continuous surjections onto standard simplices which collapse only
boundary points, so that maps out of the simplex that are constant on (part of) its boundary are
the same as maps out of the cube or the prism that are constant on the corresponding part of
their boundary.

* `Convexity.StdSimplex.ofCube n : Iⁿ → Δⁿ` sends `t` to the point with barycentric coordinates
  `(1 - t₀, t₀ (1 - t₁), t₀ t₁ (1 - t₂), …, t₀ t₁ ⋯ tₙ₋₁)`. A point of the cube lies on its
  boundary exactly when its image has a vanishing coordinate, and two points of the cube with the
  same image are equal unless both lie on the boundary. So `ofCube n` identifies `Iⁿ / ∂Iⁿ` with
  `Δⁿ / ∂Δⁿ`.
* `Convexity.StdSimplex.prism s w` maps `I × Δⁿ` onto `Δⁿ⁺¹` by splitting the vertex `0` of `Δⁿ`
  into the vertices `0` and `1` of `Δⁿ⁺¹` in the ratio `s : 1 - s`. Its ends `s = 0` and
  `s = 1` are the face maps `δ 0` and `δ 1`, and it only collapses the segments `I × {w}` with
  `w₀ = 0`.
* `Convexity.StdSimplex.splitLast c w` maps `Δⁿ × Δᵐ` to `Δⁿ⁺ᵐ` by splitting the last vertex of
  `Δⁿ` into the vertices of `Δᵐ`. It commutes with the face maps of `Δᵐ`, and it isolates the last
  coordinate of the cube: `ofCube (n + 1) t` is `ofCube n` of the first `n` coordinates of `t`,
  with its last vertex split into the edge point `ofCube 1` of the last coordinate; splitting it
  into an arbitrary edge point `ofCube 1 a` instead replaces the last coordinate of the cube by `a`.

These are the geometric inputs for comparing homotopy groups of a space defined with cubes, as in
Mathlib's `HomotopyGroup`, with those of its singular simplicial set.

## Main declarations

* `Convexity.StdSimplex.ofCube`, with `Convexity.StdSimplex.continuous_ofCube`,
  `Convexity.StdSimplex.surjective_ofCube`, `Convexity.StdSimplex.injOn_ofCube`,
  `Convexity.StdSimplex.eq_or_mem_boundary_of_ofCube_eq` and
  `Convexity.StdSimplex.exists_weights_ofCube_eq_zero_iff`.
* `Convexity.StdSimplex.prism`, with `Convexity.StdSimplex.prism_zero`,
  `Convexity.StdSimplex.prism_one`, `Convexity.StdSimplex.continuous_prism`,
  `Convexity.StdSimplex.surjective_prism` and `Convexity.StdSimplex.prism_eq_prism_iff`.
* `Convexity.StdSimplex.splitLast`, with `Convexity.StdSimplex.continuous_splitLast`,
  `Convexity.StdSimplex.splitLast_map_succAbove`, `Convexity.StdSimplex.splitLast_ofCube_init` and
  `Convexity.StdSimplex.splitLast_ofCube_init_ofCube_one`.

## References

* J. P. May, *Simplicial Objects in Algebraic Topology*, University of Chicago Press, 1967,
  §16, for the comparison of simplicial and topological homotopy groups through the realization
  of `Δⁿ / ∂Δⁿ` as a sphere.
-/

public noncomputable section

open Set unitInterval
open scoped Topology

namespace Convexity.StdSimplex

/-- The map `Iⁿ → Δⁿ` sending `t` to the point with barycentric coordinates
`(1 - t₀, t₀ (1 - t₁), t₀ t₁ (1 - t₂), …, t₀ t₁ ⋯ tₙ₋₁)`, defined by recursion on `n`: the
coordinate `0` is `1 - t₀`, and the remaining coordinates are `t₀` times those of the image of
`(t₁, …, tₙ₋₁)`. -/
def ofCube : (n : ℕ) → (I^(Fin n)) → StdSimplex ℝ (Fin (n + 1))
  | 0, _ => single 0
  | n + 1, t =>
    { weights := Finsupp.equivFunOnFinite.symm
        (Fin.cons (1 - t 0 : ℝ) fun k => (t 0 : ℝ) * (ofCube n (Fin.tail t)).weights k)
      nonneg := fun k => by
        refine Fin.cases ?_ (fun k => ?_) k
        · simpa using (t 0).2.2
        · simpa using mul_nonneg (t 0).2.1 (weights_nonneg (w := ofCube n (Fin.tail t)) k)
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simp [Fin.sum_univ_succ, ← Finset.mul_sum] }

@[simp]
lemma ofCube_weights_zero {n : ℕ} (t : I^(Fin (n + 1))) : (ofCube (n + 1) t).weights 0 = 1 - t 0 :=
  (rfl)

@[simp]
lemma ofCube_weights_succ {n : ℕ} (t : I^(Fin (n + 1))) (k : Fin (n + 1)) :
    (ofCube (n + 1) t).weights k.succ = t 0 * (ofCube n (Fin.tail t)).weights k :=
  (rfl)

/-- On the cube `I¹`, the coordinate `1` of `ofCube 1 t` is `t₀`. -/
@[simp]
lemma ofCube_one_weights_one (t : I^(Fin 1)) : (ofCube 1 t).weights 1 = t 0 := by
  simpa using ofCube_weights_succ t 0

@[fun_prop]
lemma continuous_ofCube (n : ℕ) : Continuous (ofCube n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    rw [(isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff, continuous_pi_iff]
    refine fun k => Fin.cases ?_ (fun k => ?_) k
    · simp only [Function.comp_apply, ofCube_weights_zero]
      fun_prop
    · simp only [Function.comp_apply, ofCube_weights_succ]
      have := (continuous_weights_apply ℝ k).comp
        (ih.comp (continuous_pi fun j => continuous_apply (A := fun _ => I) j.succ))
      exact (continuous_subtype_val.comp (continuous_apply 0)).mul this

/-- A point of the cube whose image in the simplex has a vanishing barycentric coordinate lies
on the boundary of the cube. -/
lemma mem_boundary_of_weights_ofCube_eq_zero {n : ℕ} {t : I^(Fin n)} {k : Fin (n + 1)}
    (h : (ofCube n t).weights k = 0) : t ∈ Cube.boundary (Fin n) := by
  induction n with
  | zero =>
    obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
    simp [ofCube] at h
  | succ n ih =>
    cases k using Fin.cases with
    | zero =>
      rw [ofCube_weights_zero] at h
      exact ⟨0, Or.inr (Subtype.ext (by simpa using (sub_eq_zero.1 h).symm))⟩
    | succ k =>
      rcases mul_eq_zero.1 ((ofCube_weights_succ t k).symm.trans h) with h | h
      · exact ⟨0, Or.inl (Subtype.ext h)⟩
      · obtain ⟨j, hj⟩ := ih h
        exact ⟨j.succ, hj⟩

/-- A point of the cube lies on its boundary exactly when its image in the simplex has a
vanishing barycentric coordinate, that is, lies on the boundary of the simplex. -/
lemma exists_weights_ofCube_eq_zero_iff {n : ℕ} {t : I^(Fin n)} :
    (∃ k, (ofCube n t).weights k = 0) ↔ t ∈ Cube.boundary (Fin n) := by
  refine ⟨fun ⟨k, hk⟩ => mem_boundary_of_weights_ofCube_eq_zero hk, fun ht => ?_⟩
  induction n with
  | zero =>
    obtain ⟨i, -⟩ := ht
    exact i.elim0
  | succ n ih =>
    obtain ⟨i, hi⟩ := ht
    cases i using Fin.cases with
    | zero =>
      rcases hi with h | h
      · exact ⟨(0 : Fin (n + 1)).succ, by rw [ofCube_weights_succ, h]; simp⟩
      · exact ⟨0, by simp [h]⟩
    | succ j =>
      obtain ⟨k, hk⟩ := ih (t := Fin.tail t) ⟨j, hi⟩
      exact ⟨k.succ, by simp [hk]⟩

/-- Two points of the cube off its boundary with the same image in the simplex are equal. -/
lemma injOn_ofCube (n : ℕ) : InjOn (ofCube n) (Cube.boundary (Fin n))ᶜ := by
  induction n with
  | zero => exact fun t _ t' _ _ => Subsingleton.elim t t'
  | succ n ih =>
    intro t ht t' ht' h
    simp only [Cube.boundary, mem_compl_iff, mem_ofPred_eq, not_exists, not_or] at ht ht'
    have h0 : t 0 = t' 0 := Subtype.ext (by simpa using congrArg (fun w => w.weights 0) h)
    have hpos : (t 0 : ℝ) ≠ 0 := fun h => (ht 0).1 (Subtype.ext h)
    have hta : Fin.tail t ∉ Cube.boundary (Fin n) := fun ⟨j, hj⟩ =>
      hj.elim (ht j.succ).1 (ht j.succ).2
    have hta' : Fin.tail t' ∉ Cube.boundary (Fin n) := fun ⟨j, hj⟩ =>
      hj.elim (ht' j.succ).1 (ht' j.succ).2
    have htail : Fin.tail t = Fin.tail t' := by
      refine ih hta hta' (ext <| Finsupp.ext fun k => ?_)
      have := congrArg (fun w => w.weights k.succ) h
      simp only [ofCube_weights_succ, h0] at this
      exact mul_left_cancel₀ (h0 ▸ hpos) this
    rw [← Fin.cons_self_tail t, ← Fin.cons_self_tail t', h0, htail]

/-- Two points of the cube with the same image in the simplex are equal, or both lie on the
boundary of the cube. -/
lemma eq_or_mem_boundary_of_ofCube_eq {n : ℕ} {t t' : I^(Fin n)} (h : ofCube n t = ofCube n t') :
    t = t' ∨ t ∈ Cube.boundary (Fin n) ∧ t' ∈ Cube.boundary (Fin n) := by
  have key : t ∈ Cube.boundary (Fin n) ↔ t' ∈ Cube.boundary (Fin n) := by
    rw [← exists_weights_ofCube_eq_zero_iff, ← exists_weights_ofCube_eq_zero_iff, h]
  by_cases ht : t ∈ Cube.boundary (Fin n)
  · exact Or.inr ⟨ht, key.1 ht⟩
  · exact Or.inl (injOn_ofCube n ht (mt key.2 ht) h)

lemma surjective_ofCube (n : ℕ) : Function.Surjective (ofCube n) := by
  induction n with
  | zero => exact fun w => ⟨default, Subsingleton.elim (α := StdSimplex ℝ (Fin 1)) _ _⟩
  | succ n ih =>
    intro w
    have hw := w.total_of_fintype
    rw [Fin.sum_univ_succ] at hw
    by_cases h1 : w.weights 0 = 1
    · -- `w` is the vertex `0`, the image of every point with `t₀ = 0`.
      refine ⟨Fin.cons 0 fun _ => 0,
        ext <| Finsupp.ext fun k => Fin.cases (by simp [h1]) (fun k => ?_) k⟩
      have hsum : ∑ i : Fin (n + 1), w.weights i.succ = 0 := by linarith
      rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => weights_nonneg (w := w) _] at hsum
      simp [hsum k]
    · -- Otherwise rescale the remaining coordinates by `1 - w₀ > 0` and recurse.
      have hlt : w.weights 0 < 1 := lt_of_le_of_ne (weights_apply_le_one w 0) h1
      have hpos : 0 < 1 - w.weights 0 := by linarith
      have hw0 := weights_nonneg (w := w) 0
      let w' : StdSimplex ℝ (Fin (n + 1)) :=
        { weights := Finsupp.equivFunOnFinite.symm fun k => w.weights k.succ / (1 - w.weights 0)
          nonneg := fun k => by simpa using div_nonneg (weights_nonneg (w := w) k.succ) hpos.le
          total := by
            rw [Finsupp.sum_fintype _ _ (by simp)]
            simp only [Finsupp.equivFunOnFinite_symm_apply_apply, div_eq_mul_inv,
              ← Finset.sum_mul]
            rw [mul_inv_eq_one₀ hpos.ne']
            linarith }
      obtain ⟨t', ht'⟩ := ih w'
      refine ⟨Fin.cons ⟨1 - w.weights 0, by linarith, by linarith⟩ t',
        ext <| Finsupp.ext fun k => ?_⟩
      refine Fin.cases (by simp) (fun k => ?_) k
      simp only [ofCube_weights_succ, Fin.cons_zero, Fin.tail_cons, ht']
      simp [w', mul_div_cancel₀ _ hpos.ne']

/-- The map `I × Δⁿ → Δⁿ⁺¹` which splits the vertex `0` of `Δⁿ` into the vertices `0` and `1` in
the ratio `s : 1 - s`: the barycentric coordinates of `prism s w` are
`(s w₀, (1 - s) w₀, w₁, …, wₙ)`. -/
def prism {n : ℕ} (s : I) (w : StdSimplex ℝ (Fin (n + 1))) : StdSimplex ℝ (Fin (n + 2)) where
  weights := Finsupp.equivFunOnFinite.symm
    (Fin.cons (s * w.weights 0) (Fin.cons ((1 - s) * w.weights 0) fun k => w.weights k.succ))
  nonneg k := by
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
    · simpa using mul_nonneg s.2.1 (weights_nonneg (w := w) 0)
    · simpa using mul_nonneg (sub_nonneg.2 s.2.2) (weights_nonneg (w := w) 0)
    · simp
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    have := w.total_of_fintype
    rw [Fin.sum_univ_succ] at this
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ]
    linarith

variable {n : ℕ}

@[simp]
lemma prism_weights_zero (s : I) (w : StdSimplex ℝ (Fin (n + 1))) :
    (prism s w).weights 0 = s * w.weights 0 :=
  (rfl)

@[simp]
lemma prism_weights_one (s : I) (w : StdSimplex ℝ (Fin (n + 1))) :
    (prism s w).weights 1 = (1 - s) * w.weights 0 :=
  (rfl)

@[simp]
lemma prism_weights_succ_succ (s : I) (w : StdSimplex ℝ (Fin (n + 1))) (k : Fin n) :
    (prism s w).weights k.succ.succ = w.weights k.succ :=
  (rfl)

/-- The end `s = 0` of `prism` is the face map `δ 0`. -/
@[simp]
lemma prism_zero (w : StdSimplex ℝ (Fin (n + 1))) :
    prism 0 w = w.map (0 : Fin (n + 2)).succAbove := by
  refine ext <| Finsupp.ext fun k => Fin.cases ?_ (fun k => ?_) k
  · rw [weights_map_succAbove_self]
    simp
  · rw [Fin.succAbove_zero, weights_map_apply_of_injective (Fin.succ_injective _)]
    refine Fin.cases (by simp) (fun k => ?_) k
    rfl

/-- The end `s = 1` of `prism` is the face map `δ 1`. -/
@[simp]
lemma prism_one (w : StdSimplex ℝ (Fin (n + 1))) :
    prism 1 w = w.map (1 : Fin (n + 2)).succAbove := by
  refine ext <| Finsupp.ext fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · rw [← Fin.succAbove_ne_zero_zero one_ne_zero,
      weights_map_apply_of_injective Fin.succAbove_right_injective]
    simp
  · rw [Fin.succ_zero_eq_one', weights_map_succAbove_self]
    simp
  · rw [show k.succ.succ = (1 : Fin (n + 2)).succAbove k.succ from
        (Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def])).symm,
      weights_map_apply_of_injective Fin.succAbove_right_injective]
    rfl

@[fun_prop]
lemma continuous_prism :
    Continuous fun p : I × StdSimplex ℝ (Fin (n + 1)) => prism p.1 p.2 := by
  rw [(isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff, continuous_pi_iff]
  refine fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · simp only [Function.comp_apply, prism_weights_zero]
    fun_prop
  · simp only [Function.comp_apply, Fin.succ_zero_eq_one', prism_weights_one]
    fun_prop
  · simp only [Function.comp_apply, prism_weights_succ_succ]
    fun_prop

lemma surjective_prism :
    Function.Surjective fun p : I × StdSimplex ℝ (Fin (n + 1)) => prism p.1 p.2 := by
  intro v
  have hv := v.total_of_fintype
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hv
  have h0 := weights_nonneg (w := v) 0
  have h1 := weights_nonneg (w := v) 1
  -- The point of `Δⁿ` merging the vertices `0` and `1` of `v`.
  let w : StdSimplex ℝ (Fin (n + 1)) :=
    { weights := Finsupp.equivFunOnFinite.symm
        (Fin.cons (v.weights 0 + v.weights 1) fun k => v.weights k.succ.succ)
      nonneg := fun k => by
        refine Fin.cases ?_ (fun k => ?_) k
        · simpa using add_nonneg h0 h1
        · simp
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Fin.sum_univ_succ, Fin.cons_zero,
          Fin.cons_succ]
        simpa [Fin.succ_zero_eq_one, add_assoc] using hv }
  have hw0 : w.weights 0 = v.weights 0 + v.weights 1 := (rfl)
  by_cases hs : v.weights 0 + v.weights 1 = 0
  · have hv0 : v.weights 0 = 0 := by linarith
    have hv1 : v.weights 1 = 0 := by linarith
    refine ⟨(0, w), ext <| Finsupp.ext fun k =>
      Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k⟩
    · rw [prism_weights_zero, hw0, hv0, hv1]
      simp
    · rw [Fin.succ_zero_eq_one', prism_weights_one, hw0, hv0, hv1]
      simp
    · rfl
  · have hpos : 0 < v.weights 0 + v.weights 1 := lt_of_le_of_ne (add_nonneg h0 h1) (Ne.symm hs)
    let s : I := ⟨v.weights 0 / (v.weights 0 + v.weights 1), div_nonneg h0 hpos.le,
      (div_le_one hpos).2 (by linarith)⟩
    refine ⟨(s, w), ext <| Finsupp.ext fun k =>
      Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k⟩
    · simp [s, hw0, div_mul_cancel₀ _ hs]
    · simp only [Fin.succ_zero_eq_one', prism_weights_one, hw0, s]
      field_simp
      ring
    · rfl

/-- Two points of the prism have the same image in `Δⁿ⁺¹` exactly when they lie on the same
segment `I × {w}` and either coincide or that segment is collapsed, because `w₀ = 0`. -/
lemma prism_eq_prism_iff {s s' : I} {w w' : StdSimplex ℝ (Fin (n + 1))} :
    prism s w = prism s' w' ↔ w = w' ∧ (s = s' ∨ w.weights 0 = 0) := by
  constructor
  · intro h
    have h0 := congrArg (fun v => v.weights 0) h
    have h1 := congrArg (fun v => v.weights 1) h
    simp only [prism_weights_zero, prism_weights_one] at h0 h1
    have hw0 : w.weights 0 = w'.weights 0 := by linarith
    have hww : w = w' := ext <| Finsupp.ext fun k => Fin.cases hw0 (fun k => by
      simpa using congrArg (fun v => v.weights k.succ.succ) h) k
    refine ⟨hww, ?_⟩
    rw [← hww] at h0
    rcases mul_eq_mul_right_iff.1 h0 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  · rintro ⟨rfl, rfl | h⟩
    · rfl
    · refine ext <| Finsupp.ext fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
      · simp [h]
      · rw [Fin.succ_zero_eq_one']
        simp [h]
      · rfl

/-- The map `Δⁿ × Δᵐ → Δⁿ⁺ᵐ` which splits the last vertex of `Δⁿ` into the vertices of `Δᵐ`: the
barycentric coordinates of `splitLast c w` are `(c₀, …, cₙ₋₁, cₙ w₀, …, cₙ wₘ)`. It is the convex
combination, with weights `c`, of the first `n` vertices of `Δⁿ⁺ᵐ` and of the copy of `w` on the
last `m + 1` vertices. -/
def splitLast {m : ℕ} (c : StdSimplex ℝ (Fin (n + 1))) (w : StdSimplex ℝ (Fin (m + 1))) :
    StdSimplex ℝ (Fin (n + m + 1)) :=
  c.iConvexComb (Fin.lastCases (w.map (Fin.natAdd n)) fun k => .single (Fin.castAdd (m + 1) k))

variable {m : ℕ}

/-- The coordinates of `splitLast c w`, read off the convex combination defining it. -/
private lemma splitLast_weights (c : StdSimplex ℝ (Fin (n + 1))) (w : StdSimplex ℝ (Fin (m + 1)))
    (k : Fin (n + m + 1)) :
    (splitLast c w).weights k = c.weights (Fin.last n) * (w.map (Fin.natAdd n)).weights k +
      ∑ i : Fin n, if Fin.castAdd (m + 1) i = k then c.weights i.castSucc else 0 := by
  rw [splitLast, iConvexComb, weights_sConvexComb, weights_map,
    Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul]),
    Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply', Fin.sum_univ_castSucc, add_comm]
  simp [Finsupp.single_apply]

@[simp]
lemma splitLast_weights_castAdd (c : StdSimplex ℝ (Fin (n + 1))) (w : StdSimplex ℝ (Fin (m + 1)))
    (k : Fin n) : (splitLast c w).weights (Fin.castAdd (m + 1) k) = c.weights k.castSucc := by
  rw [splitLast_weights, weights_map, Finsupp.mapDomain_of_notMem_range]
  · simp [Fin.castAdd_inj]
  · rintro ⟨j, hj⟩
    exact absurd congr(($hj : ℕ)) (by simp; omega)

@[simp]
lemma splitLast_weights_natAdd (c : StdSimplex ℝ (Fin (n + 1))) (w : StdSimplex ℝ (Fin (m + 1)))
    (j : Fin (m + 1)) :
    (splitLast c w).weights (Fin.natAdd n j) = c.weights (Fin.last n) * w.weights j := by
  rw [splitLast_weights, weights_map_apply_of_injective (Fin.natAdd_injective _ _)]
  exact add_eq_left.2 <| Finset.sum_eq_zero fun i _ => by simp [Fin.ext_iff]; omega

/-- `splitLast` is jointly continuous in the two simplices. -/
@[fun_prop]
lemma continuous_splitLast :
    Continuous fun p : StdSimplex ℝ (Fin (n + 1)) × StdSimplex ℝ (Fin (m + 1)) =>
      splitLast p.1 p.2 := by
  rw [(isEmbedding_toFun_comp_weights ℝ (Fin (n + m + 1))).continuous_iff, continuous_pi_iff]
  refine fun k => Fin.addCases (m := n) (n := m + 1) (fun k => ?_) (fun j => ?_) k
  · simp only [Function.comp_apply, splitLast_weights_castAdd]
    fun_prop
  · simp only [Function.comp_apply, splitLast_weights_natAdd]
    fun_prop

/-- Splitting the last vertex commutes with the face maps of the simplex replacing it. -/
@[simp]
lemma splitLast_map_succAbove (c : StdSimplex ℝ (Fin (n + 1))) (w : StdSimplex ℝ (Fin (m + 1)))
    (j : Fin (m + 2)) :
    splitLast c (w.map j.succAbove) = (splitLast c w).map (Fin.natAdd n j).succAbove := by
  refine ext <| Finsupp.ext fun k =>
    Fin.addCases (m := n) (n := m + 2) (fun k => ?_) (fun i => ?_) k
  · rw [splitLast_weights_castAdd, ← Fin.natAdd_succAbove_castAdd j k,
      weights_map_apply_of_injective Fin.succAbove_right_injective, splitLast_weights_castAdd]
  · rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i, rfl⟩
    · rw [splitLast_weights_natAdd, weights_map_succAbove_self, weights_map_succAbove_self,
        mul_zero]
    · rw [splitLast_weights_natAdd, weights_map_apply_of_injective Fin.succAbove_right_injective,
        ← Fin.natAdd_succAbove_natAdd,
        weights_map_apply_of_injective Fin.succAbove_right_injective, splitLast_weights_natAdd]

/-- If the coordinates of `c` after the first are `a` times those of `c'`, then the same holds for
`splitLast c w` and `splitLast c' w`, for `w` an edge. -/
private lemma splitLast_weights_succ {c : StdSimplex ℝ (Fin (n + 2))}
    {c' : StdSimplex ℝ (Fin (n + 1))} {a : ℝ} (hc : ∀ k, c.weights k.succ = a * c'.weights k)
    (w : StdSimplex ℝ (Fin 2)) (k : Fin (n + 2)) :
    (splitLast c w).weights k.succ = a * (splitLast c' w).weights k := by
  -- `Fin.succ` moves each block of `Fin (n + 2)` one index up. The two index identities below need
  -- the block size to be the numeral `2`: for a general block size `m`, the two sides would live in
  -- `Fin (n + m + 1)` and `Fin (n + 1 + m)`, so no `Fin.cast`-free lemma states them.
  refine Fin.addCases (m := n) (n := 2) (fun k => ?_) (fun j => ?_) k
  · rw [show (Fin.castAdd 2 k).succ = Fin.castAdd 2 k.succ from rfl,
      splitLast_weights_castAdd, splitLast_weights_castAdd, ← Fin.succ_castSucc, hc]
  · rw [show (Fin.natAdd n j).succ = Fin.natAdd (n + 1) j from Fin.ext (by simp; omega),
      splitLast_weights_natAdd, splitLast_weights_natAdd, ← Fin.succ_last, hc, mul_assoc]

/-- The last coordinate of the cube is the coordinate of an edge replacing the last vertex of the
image of the other coordinates: `ofCube (n + 1) t` is `ofCube n` of the first `n` coordinates of
`t`, with its last vertex split by `ofCube 1` of the last coordinate. -/
@[simp]
lemma splitLast_ofCube_init (t : I^(Fin (n + 1))) :
    splitLast (ofCube n (Fin.init t)) (ofCube 1 fun _ => t (Fin.last n)) = ofCube (n + 1) t := by
  induction n with
  | zero =>
    refine ext <| Finsupp.ext fun k =>
      Fin.addCases (m := 0) (n := 2) (fun k => k.elim0) (fun j => ?_) k
    rw [splitLast_weights_natAdd]
    simp [ofCube]
  | succ n ih =>
    refine ext <| Finsupp.ext fun k => Fin.cases ?_ (fun k => ?_) k
    · -- The zero coordinate lies in the first block `Fin.castAdd 2` of `Fin (n + 1 + 2)`, where
      -- `splitLast_weights_castAdd` applies: both indices have value `0`.
      have h0 : (0 : Fin (n + 1 + 1 + 1)) = Fin.castAdd 2 0 := Fin.ext (by simp)
      conv_lhs => rw [h0]
      rw [splitLast_weights_castAdd, Fin.castSucc_zero, ofCube_weights_zero, ofCube_weights_zero]
      simp only [Fin.init_def, Fin.castSucc_zero]
    · rw [splitLast_weights_succ (c' := ofCube n (Fin.init (Fin.tail t))) (a := t 0)
        (fun k => by simp [Fin.tail_init_eq_init_tail, Fin.init]),
        ofCube_weights_succ, ← ih (Fin.tail t)]
      simp [Fin.tail]

/-- Replacing the last vertex of `ofCube n` of the first `n` coordinates of `t` by the point
`(1 - a, a)` of an edge gives `ofCube (n + 1)` of `t` with its last coordinate replaced by `a`. -/
lemma splitLast_ofCube_init_ofCube_one (t : I^(Fin (n + 1))) (a : I) :
    splitLast (ofCube n (Fin.init t)) (ofCube 1 fun _ => a) =
      ofCube (n + 1) (Function.update t (Fin.last n) a) := by
  have := splitLast_ofCube_init (Function.update t (Fin.last n) a)
  rwa [Fin.init_update_last, Function.update_self] at this

end Convexity.StdSimplex
