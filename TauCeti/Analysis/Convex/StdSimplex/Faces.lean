/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
import Mathlib.LinearAlgebra.StdBasis

/-!
# Convexity and faces of the standard simplex

The weight vectors of `Convexity.StdSimplex R ι` form a convex set, and a convex combination of
two points of the standard simplex has its weight vector on the segment between theirs.

The standard basis vectors `Pi.single i 1` are affinely independent on any subset of `ι`, and the
faces of the standard simplex, the convex hulls of sets of vertices `Pi.single i 1`, consist of
weight vectors. Over a linearly ordered semifield, the face spanned by a set of vertices is
exactly the set of points of the simplex whose coordinates vanish off that set; this holds for
any index type, identifying in particular the whole simplex and each facet opposite a vertex `i`
as convex hulls of standard basis vectors.

## Main results

* `Convexity.StdSimplex.convex_range_toFun_comp_weights`: the weight vectors of the standard
  simplex form a convex set.
* `Convexity.StdSimplex.weights_convexCombPair_mem_segment`: the weight vector of a convex
  combination lies on the segment between the weight vectors.
* `TauCeti.affineIndependent_pi_single`: the coordinate vertices `Pi.single i 1` are affinely
  independent on any subset of `ι`.
* `TauCeti.convexHull_pi_single_subset_range_toFun_comp_weights`: a face of the standard simplex
  consists of weight vectors.
* `TauCeti.mem_convexHull_pi_single_iff`, `TauCeti.convexHull_range_pi_single`,
  `TauCeti.convexHull_pi_single_compl_singleton`: the face of the standard simplex spanned by a set
  of vertices consists of the points of the simplex whose coordinates vanish off that set, giving
  the whole simplex and each facet as convex hulls of coordinate vertices.
-/

public section

open Set Finset Convexity

namespace Convexity.StdSimplex

/-- The weight vectors of the standard simplex form a convex set. -/
theorem convex_range_toFun_comp_weights (R : Type*) [Semiring R] [PartialOrder R]
    [IsOrderedRing R] (X : Type*) :
    Convex R (range fun t : StdSimplex R X => ⇑t.weights) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ a b ha hb hab
  refine ⟨⟨a • s.weights + b • t.weights, ?_, ?_⟩, rfl⟩
  · intro x
    simpa using add_nonneg (mul_nonneg ha (s.nonneg x)) (mul_nonneg hb (t.nonneg x))
  · simp [Finsupp.sum_add_index', Finsupp.sum_smul_index', ← Finsupp.mul_sum, s.total, t.total,
      hab]

/-- The weight vector of a convex combination of two points of the standard simplex lies on the
segment between their weight vectors. -/
theorem weights_convexCombPair_mem_segment {R : Type*} [Semiring R] [PartialOrder R]
    [IsStrictOrderedRing R] {ι : Type*} {p q : R} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (u v : StdSimplex R ι) :
    ⇑(convexCombPair p q hp hq hpq u v).weights ∈ segment R ⇑u.weights ⇑v.weights :=
  ⟨p, q, hp, hq, hpq, by simp⟩

end Convexity.StdSimplex

namespace TauCeti

variable {R ι : Type*}

variable (R) in
/-- The standard basis vectors `Pi.single i 1` over a ring `R` are affinely independent on any
subset of `ι`. -/
theorem affineIndependent_pi_single [Ring R] [DecidableEq ι] (t : Set ι) :
    AffineIndependent R (fun j : t => (Pi.single (j : ι) 1 : ι → R)) :=
  ((Pi.linearIndependent_single_one ι R).comp Subtype.val Subtype.val_injective).affineIndependent

/-- A face of the standard simplex, the convex hull of a set of vertices `Pi.single i 1`,
consists of weight vectors of `Convexity.StdSimplex`. -/
theorem convexHull_pi_single_subset_range_toFun_comp_weights [Semiring R] [PartialOrder R]
    [IsOrderedRing R] [DecidableEq ι] (s : Set ι) :
    convexHull R ((fun i : ι => Pi.single i (1 : R)) '' s) ⊆
      range fun t : StdSimplex R ι => ⇑t.weights := by
  refine convexHull_min (fun _ hi => ?_) (StdSimplex.convex_range_toFun_comp_weights R ι)
  obtain ⟨i, _, rfl⟩ := hi
  exact StdSimplex.pi_single_mem_range_toFun_comp_weights i

/-- Membership in a face of the standard simplex, the convex hull of a set of vertices
`Pi.single i 1`, is membership in the standard simplex together with vanishing of the coordinates
outside the face. The empty face has empty convex hull. -/
@[simp]
theorem mem_convexHull_pi_single_iff [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq ι] {s : Set ι} {x : ι → R} :
    x ∈ convexHull R ((fun i : ι => Pi.single i (1 : R)) '' s) ↔
      x ∈ (range fun t : StdSimplex R ι => ⇑t.weights) ∧ ∀ i ∉ s, x i = 0 := by
  constructor
  · intro hx
    refine ⟨convexHull_pi_single_subset_range_toFun_comp_weights s hx, fun i hi => ?_⟩
    apply convexHull_min (fun _ hz => ?_) (convex_hyperplane (LinearMap.proj i).isLinear 0) hx
    obtain ⟨j, hj, rfl⟩ := hz
    simp [ne_of_mem_of_not_mem hj hi]
  · rintro ⟨⟨t, rfl⟩, hsupp⟩
    classical
    -- Split off one vertex at a time, by induction on the number of vertices carrying weight.
    induction hn : #t.weights.support using Nat.strong_induction_on generalizing t with
    | _ n ih =>
    obtain ⟨a, ha⟩ := t.support_weights_nonempty
    have has : a ∈ s := by_contra fun h => Finsupp.mem_support_iff.mp ha (hsupp a h)
    have hva : (Pi.single a 1 : ι → R) ∈ convexHull R ((fun i : ι => Pi.single i (1 : R)) '' s) :=
      subset_convexHull R _ ⟨a, has, rfl⟩
    by_cases hs' : ∃ j ∈ ({a}ᶜ : Set ι), t.weights j ≠ 0
    · -- `t` lies on the segment from the vertex `a` to its restriction away from `a`.
      rw [← t.convexCombPair_restrict_restrict_compl {a} ⟨a, rfl, Finsupp.mem_support_iff.mp ha⟩
        hs']
      refine (convex_convexHull R _).segment_subset ?_ ?_
        (StdSimplex.weights_convexCombPair_mem_segment ..)
      · simpa [Finsupp.single_eq_pi_single] using hva
      · refine ih _ ?_ _ (fun j hj => ?_) rfl
        · rw [← hn, StdSimplex.support_weights_restrict]
          exact card_lt_card (filter_ssubset.mpr ⟨a, ha, by simp⟩)
        · exact Finsupp.notMem_support_iff.mp (by simp [hsupp j hj])
    · -- Otherwise `t` is the vertex `a`.
      push Not at hs'
      simpa [StdSimplex.eq_single_of_forall_ne_weights_eq_zero hs', Finsupp.single_eq_pi_single]
        using hva

/-- The convex hull of all standard basis vectors `Pi.single i 1` over a linearly ordered
semifield is the standard simplex. -/
theorem convexHull_range_pi_single [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq ι] :
    convexHull R (range fun i : ι => (Pi.single i 1 : ι → R)) =
      range fun s : StdSimplex R ι => ⇑s.weights := by
  rw [← image_univ]
  ext x
  rw [mem_convexHull_pi_single_iff]
  simp

/-- The convex hull of the standard basis vectors other than `i` over a linearly ordered semifield
is the facet opposite `i`. -/
theorem convexHull_pi_single_compl_singleton [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq ι] (i : ι) :
    convexHull R ((fun j : ι => (Pi.single j 1 : ι → R)) '' {i}ᶜ) =
      {y ∈ range fun s : StdSimplex R ι => ⇑s.weights | y i = 0} := by
  ext y
  rw [mem_convexHull_pi_single_iff, mem_sep_iff]
  simp

end TauCeti
