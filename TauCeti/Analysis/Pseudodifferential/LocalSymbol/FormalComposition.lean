/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Classical
public import TauCeti.Analysis.Pseudodifferential.Symbol.FormalComposition

/-!
# The formal composition of homogeneous symbol expansions on an open set

For an open set `U ⊆ ℝⁿ` of positions, the classical symbols on `U`
(`TauCeti.LocalClassicalSymbol`) are the full symbols of classical pseudodifferential operators
read in a chart of a manifold. The symbol of a composition of two such operators has the
expansion `b # a ∼ ∑_α ((1/i)^|α| / α!) ∂_ξ^α b ∂_x^α a`, whose terms only involve derivatives of
the factors at the same position. So the formal composition of expansions makes sense on `U`, with
no extension of the terms to `ℝⁿ`. This file sets it up, as on `ℝⁿ`
(`TauCeti/Analysis/Pseudodifferential/Symbol/FormalComposition.lean`).

* `TauCeti.LocalHomogeneousSymbol.sharpTerm k b a`: the homogeneous symbol
  `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a` of degree `m' + m - k` on `U`, summed over the words
  `w` of length `k` in the coordinate directions
  (`TauCeti.LocalHomogeneousSymbol.coefficient_sharpTerm`).
* `TauCeti.LocalClassicalSymbol.sharpTerms q p`: the homogeneous terms
  `cₖ = ∑_{i + j + r = k} sharpTerm r qᵢ pⱼ` of the formal composition of two expansions on `U`.

Both commute with restriction to smaller open sets
(`TauCeti.LocalHomogeneousSymbol.restrict_sharpTerm`,
`TauCeti.LocalClassicalSymbol.restrict_sharpTerms`), and with the restriction of homogeneous
symbols on `ℝⁿ` to `U` (`TauCeti.HomogeneousSymbol.restrict_sharpTerm`,
`TauCeti.ClassicalSymbol.restrict_sharpTerms`): on `U` they are the formal composition on `ℝⁿ`
read on `U`. This is what lets formal compositions computed in two charts be compared on their
overlap.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (2.5)–(2.7).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Finset Filter Topology

namespace TauCeti

variable {n : ℕ} {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] {m : ℝ}

namespace LocalHomogeneousSymbol

/-- The homogeneous symbol `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a` of degree `m' + m - k` on
`U`, the part of the formal composition `b # a` with `k` derivatives on each factor. It is defined
by the recursion `sharpTerm 0 b a = b ∘ a` and
`sharpTerm (k + 1) b a = (-i / (k + 1)) ∑ⱼ sharpTerm k (∂_{ξⱼ} b) (∂_{xⱼ} a)`; the closed form is
`TauCeti.LocalHomogeneousSymbol.coefficient_sharpTerm`. -/
def sharpTerm : (k : ℕ) → {m' : ℝ} → LocalHomogeneousSymbol U W Y m' →
    LocalHomogeneousSymbol U V W m → LocalHomogeneousSymbol U V Y (m' + m - k)
  | 0, _, b, a => (b.comp a).castDegree (by simp)
  | k + 1, _, b, a => (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (sharpTerm k (b.frequencyDeriv (EuclideanSpace.single j 1))
        (a.spatialDeriv (EuclideanSpace.single j 1))).castDegree (by push_cast; ring)

variable {m' : ℝ} (b : LocalHomogeneousSymbol U W Y m') (a : LocalHomogeneousSymbol U V W m)

theorem sharpTerm_zero : sharpTerm 0 b a = (b.comp a).castDegree (by simp) :=
  (rfl)

theorem sharpTerm_succ (k : ℕ) :
    sharpTerm (k + 1) b a = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (sharpTerm k (b.frequencyDeriv (EuclideanSpace.single j 1))
        (a.spatialDeriv (EuclideanSpace.single j 1))).castDegree (by push_cast; ring) :=
  (rfl)

/-- Transporting the degree of the left factor transports the degree of every term of the formal
composition. -/
@[simp]
theorem sharpTerm_castDegree_left {m'' : ℝ} (h : m' = m'') (k : ℕ) :
    sharpTerm k (b.castDegree h) a = (sharpTerm k b a).castDegree (by rw [h]) := by
  subst h
  rw [castDegree_rfl, castDegree_rfl]

/-- Transporting the degree of the right factor transports the degree of every term of the formal
composition. -/
@[simp]
theorem sharpTerm_castDegree_right {m'' : ℝ} (h : m = m'') (k : ℕ) :
    sharpTerm k b (a.castDegree h) = (sharpTerm k b a).castDegree (by rw [h]) := by
  subst h
  rw [castDegree_rfl, castDegree_rfl]

@[simp]
theorem coefficient_sharpTerm_zero (p : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerm 0 b a).coefficient p = b.coefficient p ∘L a.coefficient p := by
  simp [sharpTerm_zero]

/-- At a position of `U` and a nonzero frequency, a frequency derivative along a word of the
frequency derivative `∂_{ξ_j} b` is the frequency derivative of `b` along the word extended by
`j`. -/
private theorem coordinateDeriv_frequencyDeriv (w : List (Fin n)) (j : Fin n)
    {x ξ : CoordinateSpace n} (hx : x ∈ U) (hξ : ξ ≠ 0) :
    coordinateDeriv w
        (fun η ↦ (b.frequencyDeriv (EuclideanSpace.single j 1)).coefficient (x, η)) ξ =
      coordinateDeriv (w ++ [j]) (fun η ↦ b.coefficient (x, η)) ξ := by
  rw [coordinateDeriv_append]
  refine (EventuallyEq.coordinateDeriv ?_ w).eq_of_nhds
  filter_upwards [isOpen_compl_singleton.mem_nhds hξ] with η hη
  simp [coefficient_frequencyDeriv _ _ hx hη, coordinateDeriv_cons]

/-- At a position of `U`, a spatial derivative along a word of the spatial derivative `∂_{x_j} a`
is the spatial derivative of `a` along the word extended by `j`. -/
private theorem coordinateDeriv_spatialDeriv (w : List (Fin n)) (j : Fin n)
    {x : CoordinateSpace n} (hx : x ∈ U) (ξ : CoordinateSpace n) :
    coordinateDeriv w
        (fun y ↦ (a.spatialDeriv (EuclideanSpace.single j 1)).coefficient (y, ξ)) x =
      coordinateDeriv (w ++ [j]) (fun y ↦ a.coefficient (y, ξ)) x := by
  rw [coordinateDeriv_append]
  refine (EventuallyEq.coordinateDeriv ?_ w).eq_of_nhds
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  simp [coefficient_spatialDeriv _ _ hy, coordinateDeriv_cons]

/-- **Closed form of the composition terms.** At a position of `U` and a nonzero frequency,
`sharpTerm k b a` is `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a`, the sum over the words `w` of
length `k` in the coordinate directions. -/
theorem coefficient_sharpTerm (k : ℕ) {x ξ : CoordinateSpace n} (hx : x ∈ U) (hξ : ξ ≠ 0) :
    (sharpTerm k b a).coefficient (x, ξ) =
      ((-Complex.I) ^ k / k.factorial : ℂ) • ∑ w : Fin k → Fin n,
        coordinateDeriv (List.ofFn w) (fun η ↦ b.coefficient (x, η)) ξ ∘L
          coordinateDeriv (List.ofFn w) (fun y ↦ a.coefficient (y, ξ)) x := by
  induction k generalizing m' b a with
  | zero => simp
  | succ k ih =>
    rw [sharpTerm_succ, coefficient_smul, Pi.smul_apply, coefficient_sum, Finset.sum_apply]
    simp only [coefficient_castDegree, ih, coordinateDeriv_frequencyDeriv _ _ _ hx hξ,
      coordinateDeriv_spatialDeriv _ _ _ hx, Finset.smul_sum, smul_smul]
    rw [← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    simp only [Fin.snocEquiv_apply, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The composition terms commute with restriction to a smaller open set. -/
@[simp]
theorem restrict_sharpTerm (h : U' ≤ U) (k : ℕ) :
    restrict h (sharpTerm k b a) = sharpTerm k (restrict h b) (restrict h a) := by
  induction k generalizing m' b a with
  | zero => rw [sharpTerm_zero, sharpTerm_zero, restrict_castDegree, restrict_comp]
  | succ k ih =>
    simp only [sharpTerm_succ, map_smul, map_sum, restrict_castDegree, ih,
      restrict_frequencyDeriv, restrict_spatialDeriv]

end LocalHomogeneousSymbol

/-- The composition terms commute with the restriction of homogeneous symbols on `ℝⁿ` to an open
set. -/
@[simp]
theorem HomogeneousSymbol.restrict_sharpTerm {m' : ℝ}
    (b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W Y m')
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (k : ℕ) :
    restrict U (sharpTerm k b a) =
      LocalHomogeneousSymbol.sharpTerm k (restrict U b) (restrict U a) := by
  induction k generalizing m' b a with
  | zero =>
    rw [sharpTerm_zero, LocalHomogeneousSymbol.sharpTerm_zero, restrict_castDegree, restrict_comp]
  | succ k ih =>
    simp only [sharpTerm_succ, LocalHomogeneousSymbol.sharpTerm_succ, map_smul, map_sum,
      restrict_castDegree, ih, restrict_frequencyDeriv, restrict_spatialDeriv]

namespace LocalClassicalSymbol

open LocalHomogeneousSymbol

variable {m' : ℝ}

/-- The homogeneous terms `cₖ = ∑_{i + j + r = k} ((-i)ʳ / r!) ∑_{|w| = r} ∂_ξ^w qᵢ ∘ ∂_x^w pⱼ`
of the formal composition `q # p` of two expansions on `U`, with the terms `qᵢ` of degree `m' - i`
and `pⱼ` of degree `m - j`. The term `cₖ` has degree `m' + m - k`. -/
def sharpTerms (q : (i : ℕ) → LocalHomogeneousSymbol U W Y (m' - i))
    (p : (j : ℕ) → LocalHomogeneousSymbol U V W (m - j)) (k : ℕ) :
    LocalHomogeneousSymbol U V Y (m' + m - k) :=
  ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
    if h : i + j ≤ k then
      (sharpTerm (k - (i + j)) (q i) (p j)).castDegree (by rw [Nat.cast_sub h]; push_cast; ring)
    else 0

variable (q : (i : ℕ) → LocalHomogeneousSymbol U W Y (m' - i))
  (p : (j : ℕ) → LocalHomogeneousSymbol U V W (m - j))

/-- The coefficient of `cₖ` is `∑_{i + j ≤ k} sharpTerm (k - i - j) qᵢ pⱼ`. -/
theorem coefficient_sharpTerms (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms q p k).coefficient z =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
        if i + j ≤ k then (sharpTerm (k - (i + j)) (q i) (p j)).coefficient z else 0 := by
  simp only [sharpTerms, LocalHomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

/-- The leading term of the formal composition is the composition of the leading terms. -/
@[simp]
theorem coefficient_sharpTerms_zero (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms q p 0).coefficient z = (q 0).coefficient z ∘L (p 0).coefficient z := by
  simp [coefficient_sharpTerms]

/-- The term `c_{k+1}` of the formal composition is `q_{k+1} ∘ p₀` plus terms involving only
`q₀, …, qₖ`. -/
theorem coefficient_sharpTerms_succ (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms q p (k + 1)).coefficient z =
      (q (k + 1)).coefficient z ∘L (p 0).coefficient z +
        ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 2),
          if i + j ≤ k + 1 then (sharpTerm (k + 1 - (i + j)) (q i) (p j)).coefficient z
          else 0 := by
  rw [coefficient_sharpTerms, Finset.sum_range_succ, add_comm, Finset.sum_range_succ']
  congr 1
  rw [Finset.sum_eq_zero fun j _ ↦ ite_eq_right (by omega), zero_add, ite_eq_left (by omega),
    coefficient_congr_index (fun r ↦ sharpTerm r (q (k + 1)) (p 0)) (show k + 1 - (k + 1 + 0) = 0
      by omega), coefficient_sharpTerm_zero]

/-- The term `c_{k+1}` of the formal composition is `q₀ ∘ p_{k+1}` plus terms involving only
`p₀, …, pₖ`. -/
theorem coefficient_sharpTerms_succ' (k : ℕ) (z : CoordinateSpace n × CoordinateSpace n) :
    (sharpTerms q p (k + 1)).coefficient z =
      (q 0).coefficient z ∘L (p (k + 1)).coefficient z +
        ∑ j ∈ range (k + 1), ∑ i ∈ range (k + 2),
          if i + j ≤ k + 1 then (sharpTerm (k + 1 - (i + j)) (q i) (p j)).coefficient z
          else 0 := by
  rw [coefficient_sharpTerms, Finset.sum_comm, Finset.sum_range_succ, add_comm,
    Finset.sum_range_succ']
  congr 1
  rw [Finset.sum_eq_zero fun i _ ↦ ite_eq_right (by omega), zero_add, ite_eq_left (by omega),
    coefficient_congr_index (fun r ↦ sharpTerm r (q 0) (p (k + 1))) (show k + 1 - (0 + (k + 1)) = 0
      by omega), coefficient_sharpTerm_zero]

/-- The formal composition commutes with restriction to a smaller open set. -/
@[simp]
theorem restrict_sharpTerms (h : U' ≤ U) (k : ℕ) :
    LocalHomogeneousSymbol.restrict h (sharpTerms q p k) =
      sharpTerms (fun i ↦ LocalHomogeneousSymbol.restrict h (q i))
        (fun j ↦ LocalHomogeneousSymbol.restrict h (p j)) k := by
  simp only [sharpTerms, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

end LocalClassicalSymbol

/-- The formal composition commutes with the restriction of homogeneous symbols on `ℝⁿ` to an open
set. -/
@[simp]
theorem ClassicalSymbol.restrict_sharpTerms {m' : ℝ}
    (q : (i : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W Y (m' - i))
    (p : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j))
    (k : ℕ) :
    HomogeneousSymbol.restrict U (sharpTerms q p k) =
      LocalClassicalSymbol.sharpTerms (fun i ↦ HomogeneousSymbol.restrict U (q i))
        (fun j ↦ HomogeneousSymbol.restrict U (p j)) k :=
  LocalHomogeneousSymbol.ext_of_mem fun x hx ξ _ ↦ by
    rw [HomogeneousSymbol.coefficient_restrict_of_mem _ hx, coefficient_sharpTerms,
      LocalClassicalSymbol.coefficient_sharpTerms]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp [← HomogeneousSymbol.restrict_sharpTerm, hx]

end TauCeti
