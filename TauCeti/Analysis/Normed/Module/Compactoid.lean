/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Compactoid subsets of normed spaces

A subset `S` of a seminormed space `E` over a normed field `K`, or more generally of a
seminormed group with an action of a seminormed ring `K`, is *compactoid*
(`TauCeti.IsCompactoidSet K S`) if for every `ε > 0` there are finitely many vectors
`v₁, …, vₙ` such that every `x ∈ S` lies within `ε` of a combination `∑ aᵢ • vᵢ` with all
`‖aᵢ‖ ≤ 1`. Equivalently, `S ⊆ U + {∑ aᵢ • vᵢ | ‖aᵢ‖ ≤ 1}` for every zero neighbourhood `U` and
suitable finitely many `vᵢ` (`TauCeti.isCompactoidSet_iff_forall_mem_nhds`). For a module over an
ultrametric seminormed ring with `‖1‖ = 1`, such as a seminormed space over a nonarchimedean
field, these combinations are exactly the `K°`-submodule spanned by the `vᵢ`, so the condition
reads `S ⊆ U + span_{K°} F` for some finite `F`
(`TauCeti.isCompactoidSet_iff_forall_mem_nhds_subset_add_span`).

Compactoid sets replace relatively compact sets in nonarchimedean functional analysis: over a
field such as `ℂ_p`, which is not locally compact, a bounded subset of a line need not be totally
bounded, yet it is compactoid. Operators mapping the closed unit ball to a compactoid set are the
compact operators of nonarchimedean Banach space theory. Every totally bounded set is compactoid
as soon as every vector is fixed by some scalar of norm at most one and annihilated by some scalar
of norm at most one — in particular when `‖1‖ ≤ 1`, `1 • x = x` and `0 • x = 0`, as over any
normed field. Conversely, a compactoid set is totally bounded as soon as, for each vector `v`, the
multiples `a • v` with `‖a‖ ≤ 1` form a totally bounded set: for instance over a scalar ring whose
closed unit ball is compact, such as a nontrivially normed locally compact field, when each map
`a ↦ a • v` is continuous on that ball, or in a seminormed space over `ℚ`. Under both conditions
the two notions agree (`TauCeti.isCompactoidSet_iff_totallyBounded_of_forall`,
`TauCeti.isCompactoidSet_iff_totallyBounded`).

## Main definitions

* `TauCeti.IsCompactoidSet K S`: finite approximation of `S` by combinations with coefficients
  in the closed unit ball of `K`.

## Main results

* `TauCeti.isCompactoidSet_iff_forall_mem_nhds`: the formulation through zero neighbourhoods.
* `TauCeti.isCompactoidSet_iff_forall_mem_nhds_subset_add_span`: over an ultrametric scalar ring
  with `‖1‖ = 1`, the formulation `S ⊆ U + span_{K°} F` through finite spans over the closed unit
  ball `K°`.
* `TauCeti.isCompactoidSet_of_forall_exists_finset`: approximation by finite subfamilies of a
  fixed family suffices.
* `TauCeti.IsCompactoidSet.exists_seq_forall_exists_finset`: conversely, a compactoid set is
  approximated by finite pieces of one sequence.
* `TauCeti.isCompactoidSet_of_forall_exists_norm_sub_lt`: a set approximated arbitrarily well by
  compactoid sets is compactoid.
* `TauCeti.IsCompactoidSet.mono`, `TauCeti.IsCompactoidSet.add`, `TauCeti.isCompactoidSet_sum`,
  `TauCeti.IsCompactoidSet.image`, `TauCeti.isCompactoidSet_closure_iff`: stability under subsets,
  finite sums, continuous linear images and closure.
* `TauCeti.IsCompactoidSet.union`, `TauCeti.isCompactoidSet_union_iff`,
  `TauCeti.isCompactoidSet_singleton`, `TauCeti.isCompactoidSet_insert_iff`: stability under
  finite unions (when every vector is annihilated by a scalar of norm at most one, or `0 • x = 0`
  for the `simp` equivalences), compactoidness of singletons (when `‖1‖ ≤ 1` and `1 • x = x`),
  and stability under inserting a point whose singleton is compactoid (when `0 • x = 0`).
* `TauCeti.IsCompactoidSet.image_of_forall_exists`: stability under continuous additive maps `u`
  that transport coefficients to a target scalar ring `L`: for each `a` with `‖a‖ ≤ 1` and each
  `v`, `u (a • v) = b • u v` for some `b : L` with `‖b‖ ≤ 1`.
* `TauCeti.IsCompactoidSet.smul`, `TauCeti.IsCompactoidSet.smul₀`: stability under scalar
  multiples, for a distributive action by continuous maps that commutes with itself, or of a
  normed division ring.
* `TotallyBounded.isCompactoidSet`, `Set.Finite.isCompactoidSet`: totally bounded sets, in
  particular finite sets, are compactoid when every vector is fixed by some scalar of norm at most
  one and annihilated by some scalar of norm at most one.
* `TauCeti.IsCompactoidSet.isBounded_of_forall`, `TauCeti.IsCompactoidSet.isBounded`: compactoid
  sets are bounded when the multiples `a • v` with `‖a‖ ≤ 1` of each vector form a bounded set,
  in particular for a bounded scalar action.
* `Bornology.IsBounded.isCompactoidSet`: in a finite-dimensional space over a complete nontrivially
  normed field, conversely, bounded sets are compactoid.
* `TauCeti.IsCompactoidSet.totallyBounded_of_forall`: compactoid sets are totally bounded when the
  multiples `a • v` with `‖a‖ ≤ 1` of each vector form a totally bounded set.
* `TauCeti.isCompactoidSet_iff_totallyBounded`: over a scalar ring whose closed unit ball is
  compact, such that each map `a ↦ a • v` is continuous on that ball and every vector is fixed by
  some scalar of norm at most one and annihilated by some scalar of norm at most one, compactoid
  sets are exactly the totally bounded sets.

## References

* N. De Grande-De Kimpe, *Non-archimedean nuclearity*, Groupe de travail d'analyse
  ultramétrique **9**, no. 3 (1981–1982), exp. J4, §§1.1, 2.1.
* W. H. Schikhof, *Banach spaces over nonarchimedean valued fields*, Topology Proceedings **24**
  (1999), 547–581, §§2.13, 2.15.
-/

public section

open Filter Topology Metric Pointwise

namespace TauCeti

variable {K E F : Type*}

section SeminormedRing

variable [SeminormedRing K] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

section SMul

variable [SMul K E]

variable (K) in
/-- A subset `S` of a seminormed group `E` with scalars in a seminormed ring `K` (typically a
seminormed `K`-space) is **compactoid** if for every `ε > 0` there are finitely many vectors `v i`
such that every `x ∈ S` is within `ε` of some `∑ i, a i • v i` with all `‖a i‖ ≤ 1`. -/
def IsCompactoidSet (S : Set E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (v : Fin n → E), ∀ x ∈ S,
    ∃ a : Fin n → K, (∀ i, ‖a i‖ ≤ 1) ∧ ‖x - ∑ i, a i • v i‖ < ε

/-- Unfolding `TauCeti.IsCompactoidSet`. -/
theorem isCompactoidSet_iff {S : Set E} :
    IsCompactoidSet K S ↔ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (v : Fin n → E), ∀ x ∈ S,
      ∃ a : Fin n → K, (∀ i, ‖a i‖ ≤ 1) ∧ ‖x - ∑ i, a i • v i‖ < ε :=
  Iff.rfl

/-- A set is compactoid if and only if for every neighbourhood `U` of zero there are finitely many
vectors `v i` with `S ⊆ U + {∑ i, a i • v i | ‖a i‖ ≤ 1}`. -/
theorem isCompactoidSet_iff_forall_mem_nhds {S : Set E} :
    IsCompactoidSet K S ↔ ∀ U ∈ 𝓝 (0 : E), ∃ (n : ℕ) (v : Fin n → E), ∀ x ∈ S,
      ∃ a : Fin n → K, (∀ i, ‖a i‖ ≤ 1) ∧ x - ∑ i, a i • v i ∈ U := by
  refine ⟨fun hS U hU ↦ ?_, fun hS ε hε ↦ ?_⟩
  · obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨n, v, hv⟩ := hS ε hε
    exact ⟨n, v, fun x hx ↦ (hv x hx).imp fun a ha ↦ ⟨ha.1, hεU (mem_ball_zero_iff.2 ha.2)⟩⟩
  · obtain ⟨n, v, hv⟩ := hS _ (ball_mem_nhds 0 hε)
    exact ⟨n, v, fun x hx ↦ (hv x hx).imp fun a ha ↦ ⟨ha.1, mem_ball_zero_iff.1 ha.2⟩⟩

/-- To show that `S` is compactoid it suffices to approximate it, for every `ε > 0`, by
combinations of a finite subfamily of a fixed family `v`, with coefficients of norm at most one. -/
theorem isCompactoidSet_of_forall_exists_finset {ι : Type*} {S : Set E} (v : ι → E)
    (h : ∀ ε : ℝ, 0 < ε → ∃ t : Finset ι, ∀ x ∈ S,
      ∃ a : ι → K, (∀ i, ‖a i‖ ≤ 1) ∧ ‖x - ∑ i ∈ t, a i • v i‖ < ε) :
    IsCompactoidSet K S := by
  intro ε hε
  obtain ⟨t, ht⟩ := h ε hε
  refine ⟨t.card, fun k ↦ v (t.equivFin.symm k), fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hx⟩ := ht x hx
  refine ⟨fun k ↦ a (t.equivFin.symm k), fun k ↦ ha _, ?_⟩
  rwa [Equiv.sum_comp t.equivFin.symm (fun i ↦ a i • v i), Finset.sum_coe_sort t fun i ↦ a i • v i]

/-- **A compactoid set is approximated by finite pieces of one sequence**: there is a sequence `v`
such that, for every `ε > 0`, every point of `S` is within `ε` of a combination of finitely many
fixed terms of `v` with coefficients of norm at most one. Consequently `S` lies in the closure of
the set of finite combinations of terms of `v` with coefficients of norm at most one; for a module
action, in particular, in the closure of the span of `v`. -/
theorem IsCompactoidSet.exists_seq_forall_exists_finset {S : Set E} (hS : IsCompactoidSet K S) :
    ∃ v : ℕ → E, ∀ ε : ℝ, 0 < ε → ∃ t : Finset ℕ, ∀ x ∈ S,
      ∃ a : ℕ → K, (∀ i, ‖a i‖ ≤ 1) ∧ ‖x - ∑ i ∈ t, a i • v i‖ < ε := by
  classical
  choose m w hw using fun n : ℕ ↦ isCompactoidSet_iff.1 hS (1 / (n + 1)) Nat.one_div_pos_of_nat
  -- Enumerate the approximating families for all the radii `1 / (n + 1)` at once.
  let e : (Σ n, Fin (m n)) → ℕ := Encodable.encode
  have he : Function.Injective e := Encodable.encode_injective
  refine ⟨Function.extend e (fun p ↦ w p.1 p.2) 0, fun ε hε ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨Finset.univ.image fun i : Fin (m n) ↦ e ⟨n, i⟩, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hxa⟩ := hw n x hx
  -- Keep the coefficients of the `n`-th family and put zero everywhere else.
  let b : (Σ n, Fin (m n)) → K := fun p ↦ if h : p.1 = n then a (Fin.cast (congrArg m h) p.2) else 0
  refine ⟨Function.extend e b 0, fun i ↦ ?_, ?_⟩
  · obtain ⟨p, rfl⟩ | hi := em (∃ p, e p = i)
    · rw [he.extend_apply]
      dsimp only [b]
      split_ifs <;> simp [ha]
    · simp [Function.extend_apply' _ _ _ hi]
  · have hsum : ∑ i ∈ Finset.univ.image fun i : Fin (m n) ↦ e ⟨n, i⟩, Function.extend e b 0 i •
        Function.extend e (fun p ↦ w p.1 p.2) 0 i = ∑ i, a i • w n i := by
      rw [Finset.sum_image fun i _ j _ h ↦ by simpa using he h]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [he.extend_apply, he.extend_apply]
      simp [b]
    rw [hsum]
    exact hxa.trans hn

/-- A subset of a compactoid set is compactoid. -/
theorem IsCompactoidSet.mono {S T : Set E} (hT : IsCompactoidSet K T) (hST : S ⊆ T) :
    IsCompactoidSet K S := fun ε hε ↦
  (hT ε hε).imp fun _ ↦ Exists.imp fun _ hv x hx ↦ hv x (hST hx)

/-- The empty set is compactoid. -/
@[simp]
theorem isCompactoidSet_empty : IsCompactoidSet K (∅ : Set E) :=
  fun _ _ ↦ ⟨0, Fin.elim0, by simp⟩

/-- The pointwise sum of two compactoid sets is compactoid. -/
theorem IsCompactoidSet.add {S T : Set E} (hS : IsCompactoidSet K S)
    (hT : IsCompactoidSet K T) : IsCompactoidSet K (S + T) := by
  intro ε hε
  obtain ⟨m, v, hv⟩ := hS (ε / 2) (half_pos hε)
  obtain ⟨n, w, hw⟩ := hT (ε / 2) (half_pos hε)
  refine ⟨m + n, Fin.append v w, ?_⟩
  rintro _ ⟨x, hx, y, hy, rfl⟩
  obtain ⟨a, ha, hx⟩ := hv x hx
  obtain ⟨b, hb, hy⟩ := hw y hy
  refine ⟨Fin.append a b, fun i ↦ Fin.addCases (by simpa using ha) (by simpa using hb) i, ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  calc ‖x + y - (∑ i, a i • v i + ∑ i, b i • w i)‖
      = ‖(x - ∑ i, a i • v i) + (y - ∑ i, b i • w i)‖ := by rw [add_sub_add_comm]
    _ ≤ ‖x - ∑ i, a i • v i‖ + ‖y - ∑ i, b i • w i‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hx hy
    _ = ε := add_halves ε

/-- A finite pointwise sum of compactoid sets is compactoid. -/
theorem isCompactoidSet_sum {ι : Type*} {s : Finset ι} (t : ι → Set E)
    (h : ∀ i ∈ s, IsCompactoidSet K (t i)) : IsCompactoidSet K (∑ i ∈ s, t i) :=
  Finset.sum_induction t (IsCompactoidSet K) (fun _ _ ↦ IsCompactoidSet.add)
    (fun _ _ ↦ ⟨0, Fin.elim0, fun x hx ↦ ⟨Fin.elim0, (·.elim0), by simp_all⟩⟩) h

/-- A set that lies, for every `ε > 0`, within distance `ε` of some compactoid set is compactoid.
-/
theorem isCompactoidSet_of_forall_exists_norm_sub_lt {S : Set E}
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : Set E, IsCompactoidSet K T ∧ ∀ x ∈ S, ∃ y ∈ T, ‖x - y‖ < ε) :
    IsCompactoidSet K S := by
  intro ε hε
  obtain ⟨T, hT, hST⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨n, v, hv⟩ := hT (ε / 2) (half_pos hε)
  refine ⟨n, v, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := hST x hx
  obtain ⟨a, ha, hy⟩ := hv y hy
  refine ⟨a, ha, ?_⟩
  calc ‖x - ∑ i, a i • v i‖ ≤ ‖x - y‖ + ‖y - ∑ i, a i • v i‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy hy
    _ = ε := add_halves ε

/-- The closure of a compactoid set is compactoid. -/
theorem IsCompactoidSet.closure {S : Set E} (hS : IsCompactoidSet K S) :
    IsCompactoidSet K (closure S) :=
  isCompactoidSet_of_forall_exists_norm_sub_lt fun ε hε ↦ ⟨S, hS, fun x hx ↦ by
    simpa only [← dist_eq_norm] using Metric.mem_closure_iff.1 hx ε hε⟩

/-- A set is compactoid if and only if its closure is. -/
@[simp]
theorem isCompactoidSet_closure_iff {S : Set E} :
    IsCompactoidSet K (closure S) ↔ IsCompactoidSet K S :=
  ⟨fun h ↦ h.mono subset_closure, IsCompactoidSet.closure⟩

/-- The union of two compactoid sets is compactoid, as soon as every vector is annihilated by some
scalar of norm at most one, used to pad the other family. By default this is witnessed by `0` using
`simp`, for instance for a module. -/
theorem IsCompactoidSet.union {S T : Set E} (hS : IsCompactoidSet K S) (hT : IsCompactoidSet K T)
    (h0 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = 0 := by exact fun v ↦ ⟨0, by simp, by simp⟩) :
    IsCompactoidSet K (S ∪ T) := by
  intro ε hε
  obtain ⟨m, v, hv⟩ := hS ε hε
  obtain ⟨n, w, hw⟩ := hT ε hε
  choose z hz hzv using h0
  refine ⟨m + n, Fin.append v w, ?_⟩
  rintro x (hx | hx)
  · obtain ⟨a, ha, hx⟩ := hv x hx
    refine ⟨Fin.append a fun j ↦ z (w j),
      fun i ↦ Fin.addCases (by simpa using ha) (by simpa using fun j ↦ hz (w j)) i, ?_⟩
    simpa [Fin.sum_univ_add, hzv] using hx
  · obtain ⟨b, hb, hx⟩ := hw x hx
    refine ⟨Fin.append (fun i ↦ z (v i)) b,
      fun i ↦ Fin.addCases (by simpa using fun i ↦ hz (v i)) (by simpa using hb) i, ?_⟩
    simpa [Fin.sum_univ_add, hzv] using hx

/-- A union of two sets is compactoid if and only if both are, as soon as `0 • v = 0`. The law
`0 • v = 0` (rather than the existential hypothesis of `IsCompactoidSet.union`) is kept here so
that `simp` can discharge it automatically for a module; since it is explicit, apply the
equivalence as `(isCompactoidSet_union_iff).1`. -/
@[simp]
theorem isCompactoidSet_union_iff {S T : Set E} (h0 : ∀ v : E, (0 : K) • v = 0 := by simp) :
    IsCompactoidSet K (S ∪ T) ↔ IsCompactoidSet K S ∧ IsCompactoidSet K T :=
  ⟨fun h ↦ ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩,
    fun h ↦ h.1.union h.2 fun v ↦ ⟨0, by simp, h0 v⟩⟩

/-- A singleton `{x}` is compactoid as soon as `‖1‖ ≤ 1` and `1 • x = x`. Both hypotheses are kept
in this form so that `simp` can discharge them automatically for a module over a ring with
`‖1‖ = 1`. -/
@[simp]
theorem isCompactoidSet_singleton {x : E} (hn : ‖(1 : K)‖ ≤ 1 := by simp)
    (h1 : (1 : K) • x = x := by simp) : IsCompactoidSet K {x} :=
  fun _ hε ↦ ⟨1, fun _ ↦ x, fun _ hy ↦ ⟨fun _ ↦ 1, fun _ ↦ hn, by simp_all⟩⟩

/-- Inserting a point `x` keeps a set compactoid, and conversely, as soon as `{x}` is compactoid
and `0 • v = 0`. Both hypotheses are kept in this form so that `simp` can discharge them
automatically for a module over a ring with `‖1‖ = 1`; since they are explicit, apply the
equivalence as `(isCompactoidSet_insert_iff).1`. -/
@[simp]
theorem isCompactoidSet_insert_iff {x : E} {S : Set E}
    (hx : IsCompactoidSet K {x} := by simp) (h0 : ∀ v : E, (0 : K) • v = 0 := by simp) :
    IsCompactoidSet K (insert x S) ↔ IsCompactoidSet K S := by
  rw [Set.insert_eq, isCompactoidSet_union_iff h0, and_iff_right hx]

/-- **A compactoid set is bounded** as soon as, for every vector `v`, the multiples `a • v` with
`‖a‖ ≤ 1` form a bounded set, for instance for a bounded scalar action
(`TauCeti.IsCompactoidSet.isBounded`). -/
theorem IsCompactoidSet.isBounded_of_forall
    (hK : ∀ v : E, Bornology.IsBounded ((· • v) '' closedBall (0 : K) 1)) {S : Set E}
    (hS : IsCompactoidSet K S) : Bornology.IsBounded S := by
  obtain ⟨n, v, hv⟩ := hS 1 one_pos
  choose R hR using fun i ↦ isBounded_iff_forall_norm_le.1 (hK (v i))
  refine isBounded_iff_forall_norm_le.2 ⟨∑ i, R i + 1, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hx⟩ := hv x hx
  have hsum : ‖∑ i, a i • v i‖ ≤ ∑ i, R i :=
    norm_sum_le_of_le _ fun i _ ↦ hR i _ ⟨a i, mem_closedBall_zero_iff.2 (ha i), rfl⟩
  exact (norm_le_norm_add_norm_sub' x _).trans (add_le_add hsum hx.le)

/-- A compactoid set is bounded, for a bounded scalar action. The action need not fix `0`: each
multiple `a • v` with `‖a‖ ≤ 1` stays within `‖v‖` of `(0 : K) • v`. -/
theorem IsCompactoidSet.isBounded [IsBoundedSMul K E] {S : Set E} (hS : IsCompactoidSet K S) :
    Bornology.IsBounded S := by
  refine hS.isBounded_of_forall fun v ↦ (isBounded_closedBall (x := (0 : K) • v)
    (r := dist v 0)).subset ?_
  rintro _ ⟨a, ha, rfl⟩
  exact (dist_pair_smul a 0 v).trans (mul_le_of_le_one_left dist_nonneg ha)

/-- The image of a compactoid set under a continuous additive map `u` is compactoid over a target
scalar ring `L` as soon as `u` transports coefficients: for every `a : K` with `‖a‖ ≤ 1` and
every `v` there is some `b : L` with `‖b‖ ≤ 1` and `u (a • v) = b • u v`; `b` may depend on `v`.
This covers scalar extension (such as `ℚ → ℝ`), continuous linear maps
(`TauCeti.IsCompactoidSet.image`, with `L = K` and `b = a`), and multiplication by a scalar `c`
that acts continuously and additively, with `b = a` for commuting actions
(`TauCeti.IsCompactoidSet.smul`) and `b = c * a * c⁻¹` over a normed division ring
(`TauCeti.IsCompactoidSet.smul₀`). -/
theorem IsCompactoidSet.image_of_forall_exists {L : Type*} [SeminormedRing L] [SMul L F]
    {S : Set E} (hS : IsCompactoidSet K S) (u : E →+ F) (hu : Continuous u)
    (h : ∀ a : K, ‖a‖ ≤ 1 → ∀ v : E, ∃ b : L, ‖b‖ ≤ 1 ∧ u (a • v) = b • u v) :
    IsCompactoidSet L (u '' S) := by
  rw [isCompactoidSet_iff_forall_mem_nhds] at hS ⊢
  intro U hU
  obtain ⟨n, v, hv⟩ := hS _ (hu.tendsto' 0 0 (map_zero u) hU)
  refine ⟨n, fun i ↦ u (v i), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hx⟩ := hv x hx
  choose b hb hub using h
  refine ⟨fun i ↦ b (a i) (ha i) (v i), fun i ↦ hb _ _ _, ?_⟩
  rwa [Set.mem_preimage, map_sub, map_sum,
    Finset.sum_congr rfl fun i _ ↦ hub (a i) (ha i) (v i)] at hx

end SMul

/-- **The span formulation**: over an ultrametric scalar ring with `‖1‖ = 1`, whose closed unit
ball is the subring `K°` (`Subring.unitClosedBall K`), a set is compactoid if and only if for
every neighbourhood `U` of zero there is a finite set `s` with `S ⊆ U + span_{K°} s`. -/
theorem isCompactoidSet_iff_forall_mem_nhds_subset_add_span [IsUltrametricDist K] [NormOneClass K]
    [Module K E] {S : Set E} :
    IsCompactoidSet K S ↔ ∀ U ∈ 𝓝 (0 : E), ∃ s : Finset E,
      S ⊆ U + (Submodule.span (Subring.unitClosedBall K) (s : Set E) : Set E) := by
  classical
  refine ⟨fun hS U hU ↦ ?_, fun h ↦ isCompactoidSet_of_forall_exists_finset id fun ε hε ↦ ?_⟩
  · obtain ⟨n, v, hv⟩ := isCompactoidSet_iff_forall_mem_nhds.1 hS U hU
    refine ⟨Finset.univ.image v, fun x hx ↦ ?_⟩
    obtain ⟨a, ha, hx⟩ := hv x hx
    refine ⟨_, hx, _, ?_, sub_add_cancel x _⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact Submodule.mem_span_range_iff_exists_fun _ |>.2
      ⟨fun i ↦ ⟨a i, Subring.mem_unitClosedBall.2 (ha i)⟩, by simp only [Subring.smul_def]⟩
  · obtain ⟨s, hs⟩ := h _ (ball_mem_nhds 0 hε)
    refine ⟨s, fun x hx ↦ ?_⟩
    obtain ⟨u, hu, t, ht, rfl⟩ := hs hx
    obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 ht
    exact ⟨fun v ↦ c v, fun v ↦ Subring.mem_unitClosedBall.1 (c v).property,
      by simpa [Subring.smul_def] using hu⟩

/-- The image of a compactoid set under a continuous linear map is compactoid. -/
theorem IsCompactoidSet.image [Module K E] [Module K F] {S : Set E} (hS : IsCompactoidSet K S)
    (u : E →L[K] F) : IsCompactoidSet K (u '' S) :=
  hS.image_of_forall_exists (u : E →+ F) u.continuous fun a ha v ↦ ⟨a, ha, map_smul u a v⟩

/-- A scalar multiple of a compactoid set is compactoid, for a distributive action by continuous
maps that commutes with itself. -/
theorem IsCompactoidSet.smul [DistribSMul K E] [SMulCommClass K K E] [ContinuousConstSMul K E]
    {S : Set E} (hS : IsCompactoidSet K S) (c : K) :
    IsCompactoidSet K (c • S) := by
  rw [← Set.image_smul]
  exact hS.image_of_forall_exists (DistribSMul.toAddMonoidHom E c) (continuous_const_smul c)
    fun a ha v ↦ ⟨a, ha, smul_comm c a v⟩

end SeminormedRing

/-- A scalar multiple of a compactoid set is compactoid, over a normed division ring that need not
be commutative, acting distributively by continuous maps. -/
theorem IsCompactoidSet.smul₀ [NormedDivisionRing K] [SeminormedAddCommGroup E]
    [DistribMulAction K E] [ContinuousConstSMul K E] {S : Set E} (hS : IsCompactoidSet K S)
    (c : K) : IsCompactoidSet K (c • S) := by
  rw [← Set.image_smul]
  refine hS.image_of_forall_exists (DistribSMul.toAddMonoidHom E c) (continuous_const_smul c)
    fun a ha v ↦ ⟨c * a * c⁻¹, ?_, ?_⟩ <;> rcases eq_or_ne c 0 with rfl | hc
  · simp
  · simp [norm_mul, mul_right_comm, hc, ha]
  · simp [smul_smul]
  · simp [smul_smul, hc]

section TotallyBounded

variable [SeminormedRing K] [SeminormedAddCommGroup E] [SMul K E]

/-- **A compactoid set is totally bounded** as soon as, for every vector `v`, the multiples `a • v`
with `‖a‖ ≤ 1` form a totally bounded set. This holds when the closed unit ball of `K` is compact
and each map `a ↦ a • v` is continuous on it (`TauCeti.IsCompactoidSet.totallyBounded`), and
also, for instance, for a seminormed space over `ℚ`. -/
theorem IsCompactoidSet.totallyBounded_of_forall
    (hK : ∀ v : E, TotallyBounded ((· • v) '' closedBall (0 : K) 1)) {S : Set E}
    (hS : IsCompactoidSet K S) : TotallyBounded S := by
  refine Metric.totallyBounded_iff.2 fun ε hε ↦ ?_
  obtain ⟨n, v, hv⟩ := hS (ε / 2) (half_pos hε)
  have hδ : 0 < ε / 2 / (n + 1) := by positivity
  -- Approximate each term `a i • v i` within `ε / 2 / (n + 1)` by a point of a finite set `t i`.
  choose t ht hcover using fun i ↦ Metric.totallyBounded_iff.1 (hK (v i)) _ hδ
  refine ⟨(fun y : Fin n → E ↦ ∑ i, y i) '' Set.univ.pi t, (Set.Finite.pi ht).image _,
    fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hx⟩ := hv x hx
  have hy : ∀ i, ∃ y ∈ t i, dist (a i • v i) y < ε / 2 / (n + 1) := fun i ↦ by
    simpa using hcover i ⟨a i, mem_closedBall_zero_iff.2 (ha i), rfl⟩
  choose y hyt hy using hy
  refine Set.mem_iUnion₂.2 ⟨∑ i, y i, ⟨y, fun i _ ↦ hyt i, rfl⟩, ?_⟩
  have hsum : dist (∑ i, a i • v i) (∑ i, y i) ≤ ε / 2 := by
    refine (dist_sum_sum_le_of_le _ fun i _ ↦ (hy i).le).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    linarith
  rw [mem_ball]
  calc dist x (∑ i, y i) ≤ dist x (∑ i, a i • v i) + dist (∑ i, a i • v i) (∑ i, y i) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le (by rwa [dist_eq_norm]) hsum
    _ = ε := add_halves ε

/-- Over a scalar ring whose closed unit ball is compact, for instance a nontrivially normed locally
compact field such as `ℚ_p`, every compactoid set is totally bounded as soon as each map
`a ↦ a • v` is continuous on that ball; the action need not be jointly continuous. Both hypotheses
are discharged by default for a proper scalar ring acting continuously. -/
theorem IsCompactoidSet.totallyBounded {S : Set E} (hS : IsCompactoidSet K S)
    (hK : IsCompact (closedBall (0 : K) 1) := by exact isCompact_closedBall 0 1)
    (hc : ∀ v : E, ContinuousOn (· • v) (closedBall (0 : K) 1) := by intro; fun_prop) :
    TotallyBounded S :=
  hS.totallyBounded_of_forall fun v ↦ (hK.image_of_continuousOn (hc v)).totallyBounded

end TotallyBounded

section FiniteDimensional

variable [NontriviallyNormedField K] [CompleteSpace K] [NormedAddCommGroup E] [NormedSpace K E]
  [FiniteDimensional K E]

/-- A bounded subset of a finite-dimensional normed space over a complete nontrivially normed
field is compactoid: after scaling by a scalar of large norm, its coordinates in a basis have norm
at most one. -/
theorem _root_.Bornology.IsBounded.isCompactoidSet {S : Set E} (hS : Bornology.IsBounded S) :
    IsCompactoidSet K S := by
  let b := Module.finBasis K E
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hS.image b.equivFunL.toContinuousLinearMap)
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (max M 0)
  have hc₀ : 0 < ‖c‖ := (le_max_right M 0).trans_lt hc
  refine fun ε hε ↦ ⟨_, fun i ↦ c • b i, fun x hx ↦ ⟨fun i ↦ b.repr x i * c⁻¹, fun i ↦ ?_, ?_⟩⟩
  · have hxM : ‖b.equivFunL x‖ ≤ M := by
      simpa only [ContinuousLinearEquiv.coe_coe] using hM _ ⟨x, hx, rfl⟩
    rw [norm_mul, norm_inv, mul_inv_le_iff₀ hc₀, one_mul, ← Module.Basis.equivFunL_apply]
    exact (norm_le_pi_norm (b.equivFunL x) i).trans <| hxM.trans <| (le_max_left M 0).trans hc.le
  · simpa [smul_smul, inv_mul_cancel_right₀ (norm_pos_iff.1 hc₀), b.sum_repr x] using hε

end FiniteDimensional

end TauCeti

section TotallyBounded

open TauCeti

variable {K E : Type*} [SeminormedRing K] [SeminormedAddCommGroup E] [SMul K E]

/-- A totally bounded set is compactoid, as soon as every vector is fixed by some scalar of norm at
most one and annihilated by some scalar of norm at most one, for instance over a normed field. Both
hypotheses are witnessed by `1` and `0` via `simp` by default, for instance for a module over a
ring with `‖1‖ = 1`. -/
theorem TotallyBounded.isCompactoidSet {S : Set E} (hS : TotallyBounded S)
    (h1 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = v := by exact fun v ↦ ⟨1, by simp, by simp⟩)
    (h0 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = 0 := by exact fun v ↦ ⟨0, by simp, by simp⟩) :
    IsCompactoidSet K S := by
  classical
  choose e he hev using h1
  choose z hz hzv using h0
  refine isCompactoidSet_of_forall_exists_finset id fun ε hε ↦ ?_
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 hS ε hε
  refine ⟨ht.toFinset, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  refine ⟨fun w ↦ if w = y then e y else z w, fun w ↦ ?_, ?_⟩
  · by_cases hwy : w = y <;> simp [hwy, he, hz]
  · rw [Finset.sum_eq_single_of_mem y (ht.mem_toFinset.2 hy) fun w _ hwy ↦ by simp [hwy, hzv]]
    simpa [← dist_eq_norm, hev] using hxy

/-- A finite set is compactoid, as soon as every vector is fixed by some scalar of norm at most one
and annihilated by some scalar of norm at most one. Both hypotheses are witnessed by `1` and `0`
via `simp` by default. -/
theorem Set.Finite.isCompactoidSet {S : Set E} (hS : S.Finite)
    (h1 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = v := by exact fun v ↦ ⟨1, by simp, by simp⟩)
    (h0 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = 0 := by exact fun v ↦ ⟨0, by simp, by simp⟩) :
    IsCompactoidSet K S :=
  hS.totallyBounded.isCompactoidSet h1 h0

/-- A compact set is compactoid, as soon as every vector is fixed by some scalar of norm at most
one and annihilated by some scalar of norm at most one. Both hypotheses are witnessed by `1` and
`0` via `simp` by default. -/
theorem IsCompact.isCompactoidSet {S : Set E} (hS : IsCompact S)
    (h1 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = v := by exact fun v ↦ ⟨1, by simp, by simp⟩)
    (h0 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = 0 := by exact fun v ↦ ⟨0, by simp, by simp⟩) :
    IsCompactoidSet K S :=
  hS.totallyBounded.isCompactoidSet h1 h0

/-- When every vector is fixed by some scalar of norm at most one, annihilated by some scalar of
norm at most one, and its multiples `a • v` with `‖a‖ ≤ 1` form a totally bounded set, a set is
compactoid if and only if it is totally bounded. The fixing and annihilating hypotheses are
witnessed by `1` and `0` via `simp` by default. -/
theorem TauCeti.isCompactoidSet_iff_totallyBounded_of_forall {S : Set E}
    (hK : ∀ v : E, TotallyBounded ((· • v) '' closedBall (0 : K) 1))
    (h1 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = v := by exact fun v ↦ ⟨1, by simp, by simp⟩)
    (h0 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = 0 := by exact fun v ↦ ⟨0, by simp, by simp⟩) :
    IsCompactoidSet K S ↔ TotallyBounded S :=
  ⟨IsCompactoidSet.totallyBounded_of_forall hK, (·.isCompactoidSet h1 h0)⟩

/-- Over a scalar ring whose closed unit ball is compact, such that each map `a ↦ a • v` is
continuous on that ball and every vector is fixed by some scalar of norm at most one and
annihilated by some scalar of norm at most one, a set is compactoid if and only if it is totally
bounded. All four hypotheses are discharged by default for a normed space over a proper normed
field; since they are explicit, apply the equivalence as `(isCompactoidSet_iff_totallyBounded).1`.
-/
theorem TauCeti.isCompactoidSet_iff_totallyBounded {S : Set E}
    (hK : IsCompact (closedBall (0 : K) 1) := by exact isCompact_closedBall 0 1)
    (hc : ∀ v : E, ContinuousOn (· • v) (closedBall (0 : K) 1) := by intro; fun_prop)
    (h1 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = v := by exact fun v ↦ ⟨1, by simp, by simp⟩)
    (h0 : ∀ v : E, ∃ a : K, ‖a‖ ≤ 1 ∧ a • v = 0 := by exact fun v ↦ ⟨0, by simp, by simp⟩) :
    IsCompactoidSet K S ↔ TotallyBounded S :=
  ⟨(·.totallyBounded hK hc), (·.isCompactoidSet h1 h0)⟩

end TotallyBounded
