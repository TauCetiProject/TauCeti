/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import TauCeti.Algebra.BigOperators.Finset.PartialSum
import Mathlib.Data.Finset.Sort
import TauCeti.Data.Set.Function

/-!
# Faces of the standard simplex

Complements to Mathlib's `Convexity.StdSimplex`, mostly about the maps `StdSimplex.map f`.  A point
is determined by its weight function (`StdSimplex.toFun_comp_weights_injective`), and
`StdSimplex.extendWeights p` inverts the weight function on its range, sending every other
function to the fallback point `p`.  An arbitrary map adds weights over its fibres.  An injective
map embeds a standard simplex as a face of a larger one and keeps the weights of a point, so it is
injective; a point `y` can be pulled back along any map `f` restricting to a bijection from the
full preimage of `y`'s support onto `y`'s support (`StdSimplex.comap`).  Over strict ordered
semirings, `StdSimplex.map_comap` recovers `y` under that bijection hypothesis on `y`'s support,
and `StdSimplex.comap_map` recovers `x` from `x.map f` when `f` restricts to a bijection from the
full preimage of `(x.map f)`'s support onto `(x.map f)`'s support.  For `f = j.succAbove` its image
is the facet on which the `j`-th weight vanishes; for the last vertex this facet is the smaller
simplex with a zero last weight appended.  A function taking a constant value on every facet
takes that value wherever some weight vanishes.  Two facets, opposite `j < k`, meet in the
codimension-two face opposite both: a common point of the two facets comes from that face through
both composites of face maps, the two sides of the simplicial identity
`SimplexCategory.δ_comp_δ`.

The weight vectors of the standard simplex are the vectors with nonnegative coordinates summing to
one (`StdSimplex.mem_range_toFun_comp_weights_iff`), and include the vertices `Pi.single x 1`. A
coordinate of a weight vector is less than one when another coordinate is positive, and a point
with no weight away from `x` is the vertex `x`. A linear map carrying the standard simplex into a
standard simplex preserves coordinate sums.

The prefix sums `TauCeti.prefixSum N x.weights` of the weights of a point `x` of
`StdSimplex R (Fin n)` lie between `0` and `1`. Scalar pushforward `StdSimplex.mapRange` along an
additive homomorphism sending `1` to `1` and nonnegative elements to nonnegative elements applies
the homomorphism to each weight, and over strict ordered semirings on both scalar types it commutes
with `StdSimplex.map` (`StdSimplex.mapRange_map`).

Pushing a point forward along `f` maps the support of its weights by `f`
(`StdSimplex.support_weights_map`), so every point of `StdSimplex R X` on a linear order `X` strips
uniquely along a strictly monotone map from `Fin (k + 1)` to an interior point with
nowhere-vanishing coordinates (`StdSimplex.exists_strictMono_map_eq`,
`StdSimplex.equivOfInjectiveMapEq`, `StdSimplex.eq_of_strictMono_map_eq`), and monotone maps out of
a linear order are determined by the pushforward of any interior point
(`StdSimplex.eq_of_monotone_map_eq_of_weights_ne_zero`).
-/

public section

namespace Convexity.StdSimplex

section AddCommMonoid

variable {R : Type*} [LE R] [AddCommMonoid R] [One R]

/-- A point of a standard simplex is determined by its weight function. -/
theorem toFun_comp_weights_injective {X : Type*} :
    Function.Injective fun p : StdSimplex R X ↦ (p.weights : X → R) := by
  rintro ⟨w, _, _⟩ ⟨w', _, _⟩ h
  obtain rfl : w = w' := DFunLike.coe_injective h
  rfl

variable {ι : Type*}

/-- Read a weight vector as a simplex point when it lies in the simplex, using `p` elsewhere.
This supplies probability parameters for mixtures supported on a simplex. -/
noncomputable def extendWeights (p : StdSimplex R ι) (w : ι → R) : StdSimplex R ι :=
  Function.extend (fun q : StdSimplex R ι ↦ (q.weights : ι → R)) id (fun _ ↦ p) w

/-- The inverse weight map is extended with constant fallback value `p`. -/
theorem extendWeights_def (p : StdSimplex R ι) :
    p.extendWeights =
      Function.extend (fun q : StdSimplex R ι ↦ (q.weights : ι → R)) id (fun _ ↦ p) := (rfl)

/-- Extending the inverse of the weight embedding recovers every simplex point. -/
@[simp]
theorem extendWeights_weights (p q : StdSimplex R ι) :
    p.extendWeights q.weights = q :=
  toFun_comp_weights_injective.extend_apply _ _ q

/-- Extending the inverse weight map preserves every vector in the simplex. -/
@[simp]
theorem weights_extendWeights_of_mem_range (p : StdSimplex R ι) {w : ι → R}
    (hw : w ∈ Set.range (fun q : StdSimplex R ι ↦ (q.weights : ι → R))) :
    ⇑(p.extendWeights w).weights = w := by
  obtain ⟨q, rfl⟩ := hw
  rw [extendWeights_weights]

/-- A vector outside the simplex is sent to the chosen fallback point. -/
@[simp]
theorem extendWeights_of_notMem_range (p : StdSimplex R ι) {w : ι → R}
    (hw : w ∉ Set.range (fun q : StdSimplex R ι ↦ (q.weights : ι → R))) :
    p.extendWeights w = p :=
  Function.extend_apply' _ _ _ hw

/-- A point of the triangle `StdSimplex R (Fin 3)` is determined by its three weights. -/
theorem ext_fin_three {x y : StdSimplex R (Fin 3)} (h0 : x.weights 0 = y.weights 0)
    (h1 : x.weights 1 = y.weights 1) (h2 : x.weights 2 = y.weights 2) : x = y :=
  toFun_comp_weights_injective <| funext fun | 0 => h0 | 1 => h1 | 2 => h2

/-- The three weights of a point of the standard `2`-simplex add up to `1`. -/
@[simp]
theorem total_fin_three (x : StdSimplex R (Fin 3)) :
    x.weights 0 + x.weights 1 + x.weights 2 = 1 := by
  simpa [Finsupp.sum_fintype, Fin.sum_univ_three] using x.total

/-- The weights of the last two vertices of a point of the standard `2`-simplex add up to at
most `1`. -/
theorem weights_one_add_weights_two_le_one [AddRightMono R] (x : StdSimplex R (Fin 3)) :
    x.weights 1 + x.weights 2 ≤ 1 := by
  rw [← x.total_fin_three, add_assoc]
  exact le_add_of_nonneg_left (x.nonneg 0)

variable {X Y : Type*}

/-- A point `y` of `StdSimplex R Y` pulled back to `StdSimplex R X` along a map `f : X → Y` that
restricts to a bijection from the full preimage of `y`'s support onto `y`'s support. When `R` is a
strict ordered semiring, `StdSimplex.map_comap` recovers `y` under this bijection hypothesis on
`y`'s support, and `StdSimplex.comap_map` recovers `x` from `x.map f` when `f` restricts to a
bijection from the full preimage of `(x.map f)`'s support onto `(x.map f)`'s support. -/
noncomputable def comap {f : X → Y} (y : StdSimplex R Y)
    (hf : Set.BijOn f (f ⁻¹' ↑y.weights.support) ↑y.weights.support) : StdSimplex R X where
  weights := Finsupp.comapDomain f y.weights hf.injOn
  nonneg a := by simpa using y.nonneg (f a)
  total := (Finsupp.sum_comapDomain f y.weights (fun _ r ↦ r) hf).trans y.total

/-- The weights of a pulled back point are the pulled back weights. -/
theorem weights_comap {f : X → Y} (y : StdSimplex R Y)
    (hf : Set.BijOn f (f ⁻¹' ↑y.weights.support) ↑y.weights.support) :
    (comap y hf).weights = Finsupp.comapDomain f y.weights hf.injOn :=
  (rfl)

/-- The weight of a pulled back point at `a` is the weight of the point at `f a`. -/
@[simp]
theorem weights_comap_apply {f : X → Y} (y : StdSimplex R Y)
    (hf : Set.BijOn f (f ⁻¹' ↑y.weights.support) ↑y.weights.support) (a : X) :
    (comap y hf).weights a = y.weights (f a) := by
  rw [weights_comap, Finsupp.comapDomain_apply]

end AddCommMonoid

section Semiring

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {X Y : Type*}

/-- Mapping a standard simplex adds the weights over each fibre of the map. -/
theorem weights_map_apply [Fintype X] [DecidableEq Y]
    (f : X → Y) (x : StdSimplex R X) (y : Y) :
    (x.map f).weights y = ∑ i with f i = y, x.weights i := by
  simp [weights_map, Finsupp.mapDomain_fintype, Finset.sum_apply, Finsupp.single_apply,
    Finset.sum_filter]

/-- Along an injective map, the weight at the image of a point is the weight at that point. -/
theorem weights_map_apply_of_injective {f : X → Y} (hf : f.Injective) (x : StdSimplex R X)
    (a : X) : (x.map f).weights (f a) = x.weights a :=
  Finsupp.mapDomain_apply_of_injective hf _ _

/-- The map of standard simplices along an injective map is injective. -/
theorem map_injective {f : X → Y} (hf : f.Injective) : (map (R := R) f).Injective := by
  intro x y h
  ext a
  rw [← weights_map_apply_of_injective hf, h, weights_map_apply_of_injective hf]

/-- Sums of the weights of a mapped standard simplex over the vertices in its support satisfying a
predicate equal the sum of the weights over the preimage in the original support. -/
theorem sum_filter_support_weights_map (f : X → Y) (x : StdSimplex R X)
    (P : Y → Prop) [DecidablePred P] :
    ∑ y ∈ (x.map f).weights.support.filter P, (x.map f).weights y =
      ∑ a ∈ x.weights.support.filter (fun a ↦ P (f a)), x.weights a := by
  have h := Finsupp.sum_mapDomain_index (f := f) (s := x.weights)
    (h := fun y r ↦ if P y then r else 0) (by simp) (fun _ _ _ ↦ by split_ifs <;> simp)
  simpa only [← weights_map, Finsupp.sum, ← Finset.sum_filter] using h

/-- Sums of the weights of a mapped standard simplex over a predicate on a finite vertex type
equal the sum of the weights over its preimage. -/
theorem sum_filter_weights_map [Fintype X] [Fintype Y] (f : X → Y) (x : StdSimplex R X)
    (P : Y → Prop) [DecidablePred P] :
    ∑ y ∈ Finset.univ.filter P, (x.map f).weights y =
      ∑ a ∈ Finset.univ.filter (fun a ↦ P (f a)), x.weights a := by
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Finsupp.sum_fintype (x.map f).weights (fun y r ↦ if P y then r else 0) (by simp),
    ← Finsupp.sum_fintype x.weights (fun a r ↦ if P (f a) then r else 0) (by simp)]
  simpa only [Finsupp.sum, ← Finset.sum_filter] using sum_filter_support_weights_map f x P

/-- Pulling back a point `y` along a map `f` that restricts to a bijection from the full preimage
of `y`'s support onto `y`'s support, and then mapping forward along `f`, recovers `y`. -/
@[simp]
theorem map_comap {f : X → Y} (y : StdSimplex R Y)
    (hf : Set.BijOn f (f ⁻¹' ↑y.weights.support) ↑y.weights.support) : (comap y hf).map f = y := by
  rw [← weights_inj, weights_map, weights_comap, Finsupp.mapDomain]
  exact (Finsupp.sum_comapDomain f y.weights Finsupp.single hf).trans (Finsupp.sum_single y.weights)

/-- Mapping a point `x` forward along a map `f` that restricts to a bijection from the full
preimage of `(x.map f)`'s support onto `(x.map f)`'s support, and pulling back again, recovers
`x`. -/
@[simp]
theorem comap_map {f : X → Y} (x : StdSimplex R X)
    (hf : Set.BijOn f (f ⁻¹' ↑(x.map f).weights.support) ↑(x.map f).weights.support) :
    comap (x.map f) hf = x := by
  classical
  have hS : (x.weights.support : Set X) ⊆ f ⁻¹' ↑(x.map f).weights.support := by
    rw [weights_map, Finsupp.support_mapDomain_of_nonneg x.nonneg f, Finset.coe_image]
    exact Set.subset_preimage_image f _
  ext a
  rw [weights_comap_apply]
  by_cases ha : f a ∈ (x.map f).weights.support
  · rw [weights_map, Finsupp.mapDomain_apply' _ _ hS hf.injOn ha]
  · rw [Finsupp.notMem_support_iff.mp ha, Finsupp.notMem_support_iff.mp fun h ↦ ha (hS h)]

/-- A point of a standard simplex lies on the facet opposite `j` exactly when its `j`-th weight
vanishes. -/
theorem mem_range_map_succAbove_iff {n : ℕ} (j : Fin (n + 1)) (x : StdSimplex R (Fin (n + 1))) :
    x ∈ Set.range (map (R := R) j.succAbove) ↔ x.weights j = 0 := by
  rw [mem_range_map_iff, Fin.range_succAbove]
  simp

/-- The `j`-th weight vanishes on the facet opposite `j`. -/
theorem weights_map_succAbove_self {n : ℕ} (j : Fin (n + 1)) (x : StdSimplex R (Fin n)) :
    (x.map j.succAbove).weights j = 0 :=
  (mem_range_map_succAbove_iff j _).1 ⟨x, rfl⟩

/-- On the facet opposite `j`, the weight at `j.succAbove i` is the `i`-th weight of the facet. -/
theorem weights_map_succAbove_of_eq {n : ℕ} {j k : Fin (n + 1)} {i : Fin n}
    (h : j.succAbove i = k) (x : StdSimplex R (Fin n)) :
    (x.map j.succAbove).weights k = x.weights i :=
  h ▸ weights_map_apply_of_injective Fin.succAbove_right_injective x i

/-- On the face of the standard `2`-simplex opposite the vertex `0`, the weights `w₁` and `w₂`
sum to `1`. -/
theorem weights_one_add_weights_two_map_succAbove_zero (z : StdSimplex R (Fin 2)) :
    (z.map (Fin.succAbove 0)).weights 1 + (z.map (Fin.succAbove 0)).weights 2 = 1 := by
  rw [weights_map_succAbove_of_eq (j := 0) (i := 0) (k := 1) rfl,
    weights_map_succAbove_of_eq (j := 0) (i := 1) (k := 2) rfl, total_fin_two]

omit [IsStrictOrderedRing R] in
/-- The facet of the standard simplex on `Fin (n + 1)` opposite its last vertex, the points with
vanishing last weight, is the standard simplex on `Fin n` with a zero last weight appended. -/
theorem range_snoc_weights_zero (n : ℕ) :
    (Set.range fun s : StdSimplex R (Fin n) => (Fin.snoc ⇑s.weights 0 : Fin (n + 1) → R)) =
      {y ∈ Set.range fun s : StdSimplex R (Fin (n + 1)) => ⇑s.weights | y (Fin.last n) = 0} := by
  -- Both sides are described by the nonnegativity and total of the weight functions.
  have h : (Set.range fun s : StdSimplex R (Fin n) => (Fin.snoc ⇑s.weights 0 : Fin (n + 1) → R)) =
      (fun f : Fin n → R => (Fin.snoc f 0 : Fin (n + 1) → R)) ''
        Set.range fun s : StdSimplex R (Fin n) => ⇑s.weights := by
    rw [← Set.range_comp]; rfl
  rw [h, StdSimplex.range_toFun_comp_weights, StdSimplex.range_toFun_comp_weights]
  ext y
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨f, ⟨hf₁, hf₂⟩, rfl⟩
    refine ⟨⟨fun k ↦ ?_, ?_⟩, by simp⟩
    · induction k using Fin.lastCases with
      | last => simp
      | cast j => simpa using hf₁ j
    · simpa [Fin.sum_univ_castSucc] using hf₂
  · rintro ⟨⟨h₁, h₂⟩, ht⟩
    refine ⟨Fin.init y, ⟨fun k ↦ h₁ k.castSucc, ?_⟩, ?_⟩
    · simpa [Fin.sum_univ_castSucc, Fin.init, ht] using h₂
    · simpa [ht] using Fin.snoc_init_self y

/-- A function on a standard simplex which takes the value `z` on every facet takes the value `z`
at every point with a vanishing weight. -/
theorem apply_eq_of_weights_eq_zero {n : ℕ} {Z : Type*} {φ : StdSimplex R (Fin (n + 1)) → Z}
    {z : Z} (hφ : ∀ (i : Fin (n + 1)) (w : StdSimplex R (Fin n)), φ (w.map i.succAbove) = z)
    {b : StdSimplex R (Fin (n + 1))} {k : Fin (n + 1)} (hb : b.weights k = 0) : φ b = z := by
  obtain ⟨w, rfl⟩ := (mem_range_map_succAbove_iff k b).2 hb
  exact hφ k w

/-- The facets of a standard simplex opposite `j < k` meet in the codimension-two face opposite
both: a common point is the image of a point `w` of that face, and the corresponding points of
the two facets are the images of `w` under the face maps given by the simplicial identity. -/
theorem exists_map_succAbove_of_map_succAbove_eq {n : ℕ} {j k : Fin (n + 2)} (hjk : j < k)
    {y z : StdSimplex R (Fin (n + 1))} (h : y.map j.succAbove = z.map k.succAbove) :
    ∃ w : StdSimplex R (Fin n),
      y = w.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove ∧
        z = w.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove := by
  have hy : y.weights (k.pred (Fin.ne_zero_of_lt hjk)) = 0 := by
    rw [← weights_map_apply_of_injective Fin.succAbove_right_injective (f := j.succAbove),
      Fin.succAbove_pred_of_lt _ _ hjk, h, weights_map_succAbove_self]
  obtain ⟨w, rfl⟩ := (mem_range_map_succAbove_iff _ y).2 hy
  refine ⟨w, rfl, map_injective (R := R) Fin.succAbove_right_injective (f := k.succAbove) ?_⟩
  -- The simplicial identity `SimplexCategory.δ_comp_δ`, in Mathlib's `Fin.succAbove` form.
  have hcomp : k.succAbove ∘ (j.castPred (Fin.ne_last_of_lt hjk)).succAbove =
      j.succAbove ∘ (k.pred (Fin.ne_zero_of_lt hjk)).succAbove := by
    funext m
    have hle : j ≤ (k.pred (Fin.ne_zero_of_lt hjk)).castSucc := by
      rwa [Fin.le_castSucc_iff, Fin.succ_pred]
    have := Fin.succAbove_succAbove_succAbove_predAbove j (k.pred (Fin.ne_zero_of_lt hjk)) m
    rwa [Fin.succAbove_pred_of_lt _ _ hjk, Fin.predAbove_of_le_castSucc _ _ hle] at this
  rw [← h, ← map_comp, ← hcomp, map_comp]

end Semiring

section WeightVectors

variable {R : Type*} [AddCommMonoid R] [One R]

/-- A vector is a weight vector of the standard simplex if and only if its coordinates are
nonnegative and sum to one. Mathlib's `StdSimplex.range_toFun_comp_weights` states this over
semirings. -/
theorem mem_range_toFun_comp_weights_iff [LE R] {X : Type*} [Fintype X] {x : X → R} :
    x ∈ (Set.range fun t : StdSimplex R X => ⇑t.weights) ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
  refine ⟨?_, fun ⟨h0, h1⟩ => ⟨⟨Finsupp.equivFunOnFinite.symm x, h0, ?_⟩, by simp⟩⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t.nonneg, by simpa [Finsupp.sum_fintype] using t.total⟩
  · simpa [Finsupp.sum_fintype] using h1

/-- The vertex `Pi.single x 1` is a weight vector of the standard simplex. -/
theorem pi_single_mem_range_toFun_comp_weights [Preorder R] [ZeroLEOneClass R] {X : Type*}
    [DecidableEq X] (x : X) :
    Pi.single x (1 : R) ∈ Set.range fun t : StdSimplex R X => ⇑t.weights :=
  ⟨⟨.single x 1, by simp, by simp⟩, Finsupp.single_eq_pi_single x 1⟩

/-- A coordinate of a point of the standard simplex is less than one if some other coordinate
is positive. -/
theorem apply_lt_one_of_mem_range_weights [PartialOrder R] [AddLeftStrictMono R] {ι : Type*}
    {x : ι → R} (hx : x ∈ Set.range fun s : StdSimplex R ι => ⇑s.weights) {i j : ι}
    (hij : j ≠ i) (hxj : 0 < x j) : x i < 1 := by
  classical
  have := addLeftMono_of_addLeftStrictMono R
  obtain ⟨s, rfl⟩ := hx
  -- The total weight is the sum over any finite set containing the support, here one that also
  -- contains `i` and `j`.
  have hsupp : s.weights.support ⊆ s.weights.support ∪ {i, j} := Finset.subset_union_left
  have hij' : ({i, j} : Finset ι) ⊆ s.weights.support ∪ {i, j} := Finset.subset_union_right
  have htotal := s.total
  rw [s.weights.sum_of_support_subset hsupp _ fun _ _ => rfl] at htotal
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hij' fun k _ _ => s.nonneg k
  rw [Finset.sum_pair hij.symm, htotal] at hle
  exact (lt_add_of_pos_right _ hxj).trans_le hle

end WeightVectors

/-- A point of the standard simplex with no weight away from `x` is the vertex `x`. -/
theorem eq_single_of_forall_ne_weights_eq_zero {R : Type*} [Semiring R] [PartialOrder R]
    [IsStrictOrderedRing R] {ι : Type*} {w : StdSimplex R ι} {x : ι}
    (h : ∀ y ≠ x, w.weights y = 0) : w = single x :=
  support_weights_eq_singleton.mp <| w.support_weights_nonempty.subset_singleton_iff.mp <|
    Finset.coe_subset.mp <| (Finset.coe_singleton x).symm ▸ Finsupp.support_subset_iff.mpr h

/-- A linear map carrying the weight vectors of the standard simplex on `α` into those of the
standard simplex on `β` preserves coordinate sums: it sends every vertex to a vector of coordinate
sum one. -/
theorem _root_.LinearMap.sum_apply_eq_of_mapsTo_range_weights {R : Type*} [Semiring R]
    [Preorder R] [ZeroLEOneClass R] {α β : Type*} [Fintype α] [Fintype β]
    (L : (α → R) →ₗ[R] (β → R))
    (hL : Set.MapsTo L (Set.range fun t : StdSimplex R α => ⇑t.weights)
      (Set.range fun t : StdSimplex R β => ⇑t.weights)) (v : α → R) :
    ∑ b, L v b = ∑ a, v a := by
  classical
  have hvert (a : α) : ∑ b, L (Pi.single a 1) b = 1 :=
    (mem_range_toFun_comp_weights_iff.1 (hL (pi_single_mem_range_toFun_comp_weights a))).2
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp_rw [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hvert, mul_one]

section PrefixSum

variable {R : Type*} [Preorder R] [AddCommMonoid R] [IsOrderedAddMonoid R] [One R]

/-- The prefix sums of the weights of a point of a standard simplex on `Fin n` are
nonnegative. -/
theorem prefixSum_weights_nonneg {n : ℕ} (x : StdSimplex R (Fin n)) (N : ℕ) :
    0 ≤ TauCeti.prefixSum N x.weights := by
  rw [TauCeti.prefixSum_def]
  exact Finset.sum_nonneg fun j _ ↦ x.nonneg j

/-- The prefix sums of the weights of a point of a standard simplex on `Fin n` are at most `1`. -/
theorem prefixSum_weights_le_one {n : ℕ} (x : StdSimplex R (Fin n)) (N : ℕ) :
    TauCeti.prefixSum N x.weights ≤ 1 := by
  have : TauCeti.prefixSum N x.weights ≤ TauCeti.prefixSum (max N n) x.weights :=
    TauCeti.monotone_prefixSum x.nonneg (le_max_left N n)
  rw [TauCeti.prefixSum_of_le (le_max_right _ _)] at this
  exact this.trans_eq (by simpa [Finsupp.sum_fintype] using x.total)

end PrefixSum

section MapRange

variable {R S T X Y : Type*} [LE R] [AddCommMonoid R] [One R] [LE S] [AddCommMonoid S] [One S]
  [LE T] [AddCommMonoid T] [One T]

/-- Push a point of a standard simplex forward along an additive homomorphism on its weights which
sends `1` to `1` and nonnegative elements to nonnegative elements, such as casting rational
barycentric coordinates into an ordered field. -/
noncomputable def mapRange (f : R →+ S) (hf₁ : f 1 = 1) (hf : ∀ r, 0 ≤ r → 0 ≤ f r)
    (w : StdSimplex R X) : StdSimplex S X where
  weights := w.weights.mapRange f (map_zero f)
  nonneg x := by simpa using hf _ (w.nonneg x)
  total := by
    rw [Finsupp.sum_mapRange_index (by simp), ← map_finsuppSum f w.weights fun _ r ↦ r,
      w.total, hf₁]

/-- Scalar pushforward applies `Finsupp.mapRange` to the weight vector. -/
theorem weights_mapRange (f : R →+ S) (hf₁ : f 1 = 1) (hf : ∀ r, 0 ≤ r → 0 ≤ f r)
    (w : StdSimplex R X) : (w.mapRange f hf₁ hf).weights = w.weights.mapRange f (map_zero f) :=
  (rfl)

/-- Scalar pushforward applies the homomorphism to each weight. -/
@[simp]
theorem weights_mapRange_apply (f : R →+ S) (hf₁ : f 1 = 1) (hf : ∀ r, 0 ≤ r → 0 ≤ f r)
    (w : StdSimplex R X) (x : X) : (w.mapRange f hf₁ hf).weights x = f (w.weights x) := by
  rw [weights_mapRange, Finsupp.mapRange_apply]

/-- Scalar pushforward along a homomorphism which is injective on nonnegative elements is
injective. -/
theorem mapRange_injective {f : R →+ S} (hf₁ : f 1 = 1) (hf : ∀ r, 0 ≤ r → 0 ≤ f r)
    (hfinj : Set.InjOn f {r | 0 ≤ r}) :
    Function.Injective (mapRange (X := X) f hf₁ hf) := fun w₁ w₂ h ↦
  toFun_comp_weights_injective <| funext fun x ↦
    hfinj (w₁.nonneg x) (w₂.nonneg x) <| by simpa using congr(($h).weights x)

/-- Scalar pushforward along a homomorphism which sends no nonzero nonnegative element to `0`
preserves the support of weights. -/
@[simp]
theorem support_weights_mapRange {f : R →+ S} (hf₁ : f 1 = 1) (hf : ∀ r, 0 ≤ r → 0 ≤ f r)
    (hf₀ : ∀ r, 0 ≤ r → f r = 0 → r = 0) (w : StdSimplex R X) :
    (w.mapRange f hf₁ hf).weights.support = w.weights.support := by
  ext x
  simp only [Finsupp.mem_support_iff, weights_mapRange_apply]
  exact ⟨fun h h₀ ↦ h (h₀ ▸ map_zero f), fun h h₀ ↦ h (hf₀ _ (w.nonneg x) h₀)⟩

/-- Scalar pushforward along the identity homomorphism is the identity. -/
@[simp]
theorem mapRange_id (w : StdSimplex R X) : w.mapRange (AddMonoidHom.id R) rfl (fun _ ↦ id) = w :=
  toFun_comp_weights_injective <| funext fun _ ↦ by simp

/-- Scalar pushforward preserves composition of homomorphisms. -/
theorem mapRange_comp (g : S →+ T) (hg₁ : g 1 = 1) (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (f : R →+ S)
    (hf₁ : f 1 = 1) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (w : StdSimplex R X) :
    (w.mapRange f hf₁ hf).mapRange g hg₁ hg =
      w.mapRange (g.comp f) ((congrArg g hf₁).trans hg₁) (fun r hr ↦ hg _ (hf r hr)) :=
  toFun_comp_weights_injective <| funext fun _ ↦ by simp

end MapRange

section MapRangeOrderedSemiring

variable {R S X Y : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [PartialOrder S]
  [Semiring S] [IsStrictOrderedRing S]

/-- Scalar pushforward sends each vertex point mass to the corresponding vertex point mass. -/
@[simp]
theorem mapRange_single (f : R →+ S) (hf₁ : f 1 = 1) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (x : X) :
    (single x).mapRange f hf₁ hf = single x := by
  ext y
  by_cases h : x = y <;> simp [h, hf₁]

/-- Scalar pushforward commutes with pushing vertices forward along a map. -/
theorem mapRange_map (f : R →+ S) (hf₁ : f 1 = 1) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (g : X → Y)
    (w : StdSimplex R X) :
    (w.map g).mapRange f hf₁ hf = (w.mapRange f hf₁ hf).map g := by
  apply StdSimplex.ext
  rw [weights_mapRange, weights_map, weights_map, weights_mapRange]
  exact (Finsupp.mapDomain_mapRange g w.weights f (map_zero f) (map_add f)).symm

end MapRangeOrderedSemiring

section Semiring

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {X Y : Type*}

/-- Pushing a point of a standard simplex forward along `f` maps the support of its weights. -/
theorem support_weights_map [DecidableEq Y] (f : X → Y) (x : StdSimplex R X) :
    (x.map f).weights.support = x.weights.support.image f := by
  rw [weights_map, Finsupp.support_mapDomain_of_nonneg x.nonneg]

/-- When every coordinate of `x` is nonzero, the nonzero coordinates of `x.map f` are `range f`. -/
theorem weights_map_ne_zero_iff (f : X → Y) {x : StdSimplex R X}
    (hx : ∀ i, x.weights i ≠ 0) (y : Y) :
    (x.map f).weights y ≠ 0 ↔ y ∈ Set.range f := by
  classical
  rw [← Finsupp.mem_support_iff, support_weights_map, Finset.mem_image]; simp [hx]

/-- Pushing an interior point of a standard simplex along a surjection preserves nonzero weights. -/
theorem weights_map_ne_zero_of_surjective {f : X → Y} (hf : f.Surjective)
    {x : StdSimplex R X} (hx : ∀ i, x.weights i ≠ 0) (y : Y) : (x.map f).weights y ≠ 0 :=
  (weights_map_ne_zero_iff f hx y).2 (hf y)

/-- Two maps pushing interior points of standard simplices to the same point have equal ranges. -/
theorem range_eq_of_map_eq {Z : Type*} {f₁ : X → Z} {x₁ : StdSimplex R X}
    (hx₁ : ∀ i, x₁.weights i ≠ 0) {f₂ : Y → Z} {x₂ : StdSimplex R Y}
    (hx₂ : ∀ j, x₂.weights j ≠ 0) (h : x₁.map f₁ = x₂.map f₂) : Set.range f₁ = Set.range f₂ :=
  Set.ext fun z ↦ by rw [← weights_map_ne_zero_iff f₁ hx₁, ← weights_map_ne_zero_iff f₂ hx₂, h]

/-- Every point of `StdSimplex R X` on a linear order `X` is the pushforward along a strictly
monotone map `Fin (k + 1) → X` of an interior point of `StdSimplex R (Fin (k + 1))`. -/
theorem exists_strictMono_map_eq [LinearOrder X] (w : StdSimplex R X) :
    ∃ (k : ℕ) (f : Fin (k + 1) → X) (w₀ : StdSimplex R (Fin (k + 1))),
      StrictMono f ∧ (∀ j, w₀.weights j ≠ 0) ∧ w = w₀.map f := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero w.support_weights_nonempty.card_ne_zero
  let e := w.weights.support.orderEmbOfFin hk
  have hsupp : Set.BijOn e (e ⁻¹' ↑w.weights.support) ↑w.weights.support :=
    Set.bijOn_preimage_iff.2 ⟨e.injective.injOn, by rw [Finset.range_orderEmbOfFin]⟩
  refine ⟨k, e, comap w hsupp, e.strictMono, ?_, (map_comap w hsupp).symm⟩
  intro j
  rw [weights_comap_apply]
  exact Finsupp.mem_support_iff.1 (w.weights.support.orderEmbOfFin_mem hk j)

/-- Two injective maps pushing interior points of standard simplices to the same point induce an
equivalence between their domains intertwining the maps. -/
noncomputable def equivOfInjectiveMapEq {Z : Type*} {f₁ : X → Z} (hf₁ : f₁.Injective)
    {w₁ : StdSimplex R X} (hw₁ : ∀ i, w₁.weights i ≠ 0) {f₂ : Y → Z} (hf₂ : f₂.Injective)
    {w₂ : StdSimplex R Y} (hw₂ : ∀ j, w₂.weights j ≠ 0) (h : w₁.map f₁ = w₂.map f₂) :
    X ≃ Y :=
  ((Equiv.ofInjective f₁ hf₁).trans (Set.equivOfEq (range_eq_of_map_eq hw₁ hw₂ h))).trans
    (Equiv.ofInjective f₂ hf₂).symm

/-- `equivOfInjectiveMapEq` intertwines `f₂` with `f₁`. -/
-- Not `@[simp]`: LHS has free variable `f₂` as head symbol (`warning.simp.varHead`).
theorem apply_equivOfInjectiveMapEq {Z : Type*} {f₁ : X → Z} (hf₁ : f₁.Injective)
    {w₁ : StdSimplex R X} (hw₁ : ∀ i, w₁.weights i ≠ 0) {f₂ : Y → Z} (hf₂ : f₂.Injective)
    {w₂ : StdSimplex R Y} (hw₂ : ∀ j, w₂.weights j ≠ 0) (h : w₁.map f₁ = w₂.map f₂) (x : X) :
    f₂ (equivOfInjectiveMapEq hf₁ hw₁ hf₂ hw₂ h x) = f₁ x := by
  simp [equivOfInjectiveMapEq, Equiv.apply_ofInjective_symm]

/-- The inverse of `equivOfInjectiveMapEq` intertwines `f₁` with `f₂`. -/
-- Not `@[simp]`: LHS has free variable `f₁` as head symbol (`warning.simp.varHead`).
theorem apply_equivOfInjectiveMapEq_symm {Z : Type*} {f₁ : X → Z} (hf₁ : f₁.Injective)
    {w₁ : StdSimplex R X} (hw₁ : ∀ i, w₁.weights i ≠ 0) {f₂ : Y → Z} (hf₂ : f₂.Injective)
    {w₂ : StdSimplex R Y} (hw₂ : ∀ j, w₂.weights j ≠ 0) (h : w₁.map f₁ = w₂.map f₂) (y : Y) :
    f₁ ((equivOfInjectiveMapEq hf₁ hw₁ hf₂ hw₂ h).symm y) = f₂ y := by
  simp [equivOfInjectiveMapEq, Equiv.apply_ofInjective_symm]

/-- Two injective maps out of `Fin (k₁ + 1)` and `Fin (k₂ + 1)` pushing interior points of
standard simplices to the same point have equal domain dimensions `k₁ = k₂`. -/
theorem eq_of_injective_map_eq_fin {Z : Type*} {k₁ k₂ : ℕ}
    {f₁ : Fin (k₁ + 1) → Z} (hf₁ : f₁.Injective)
    {w₁ : StdSimplex R (Fin (k₁ + 1))} (hw₁ : ∀ i, w₁.weights i ≠ 0)
    {f₂ : Fin (k₂ + 1) → Z} (hf₂ : f₂.Injective)
    {w₂ : StdSimplex R (Fin (k₂ + 1))} (hw₂ : ∀ j, w₂.weights j ≠ 0)
    (h : w₁.map f₁ = w₂.map f₂) : k₁ = k₂ :=
  Nat.succ.inj (by simpa using Fintype.card_congr (equivOfInjectiveMapEq hf₁ hw₁ hf₂ hw₂ h))

/-- A strictly monotone map from a linear order pushing an interior point to a given point of a
standard simplex is uniquely determined together with the interior point. -/
theorem eq_of_strictMono_map_eq [LinearOrder X] [Preorder Y]
    {f₁ f₂ : X → Y} (hf₁ : StrictMono f₁) (hf₂ : StrictMono f₂)
    {w₁ w₂ : StdSimplex R X} (hw₁ : ∀ i, w₁.weights i ≠ 0) (hw₂ : ∀ i, w₂.weights i ≠ 0)
    (h : w₁.map f₁ = w₂.map f₂) : f₁ = f₂ ∧ w₁ = w₂ := by
  let : Fintype X := ⟨w₁.weights.support, fun i ↦ Finsupp.mem_support_iff.2 (hw₁ i)⟩
  obtain rfl := (StrictMono.range_inj_of_wellFoundedLT hf₁ hf₂).1 (range_eq_of_map_eq hw₁ hw₂ h)
  exact ⟨rfl, map_injective hf₁.injective h⟩

/-- Monotone maps from a linear order into a partial order are determined by the pushforward
of any interior point of `StdSimplex R X`. -/
theorem eq_of_monotone_map_eq_of_weights_ne_zero [LinearOrder X] [PartialOrder Y]
    {f₁ f₂ : X → Y} (hf₁ : Monotone f₁) (hf₂ : Monotone f₂)
    {w : StdSimplex R X} (hw : ∀ a, w.weights a ≠ 0) (h : w.map f₁ = w.map f₂) : f₁ = f₂ := by
  let : Fintype X := ⟨w.weights.support, fun a ↦ Finsupp.mem_support_iff.2 (hw a)⟩
  classical
  have hpos (a : X) : 0 < w.weights a := lt_of_le_of_ne (w.nonneg a) (hw a).symm
  have hset (y : Y) :
      Finset.univ.filter (f₁ · ≤ y) = Finset.univ.filter (f₂ · ≤ y) := by
    let χ : Y → Fin 2 := fun z ↦ if z ≤ y then 0 else 1
    have hmap (g : X → Y) : ((w.map g).map χ).weights 0 =
        ∑ a ∈ Finset.univ.filter (g · ≤ y), w.weights a := by
      rw [StdSimplex.map_map, weights_map_apply]
      simp [χ]
    have hsum : ∑ a ∈ Finset.univ.filter (f₁ · ≤ y), w.weights a =
        ∑ a ∈ Finset.univ.filter (f₂ · ≤ y), w.weights a := by rw [← hmap f₁, ← hmap f₂, h]
    have hsub {g₁ g₂ : X → Y} (hg₁ : Monotone g₁) (hg₂ : Monotone g₂)
        (hle : ∑ a ∈ Finset.univ.filter (g₁ · ≤ y), w.weights a ≤
          ∑ a ∈ Finset.univ.filter (g₂ · ≤ y), w.weights a) :
        Finset.univ.filter (g₁ · ≤ y) ⊆ Finset.univ.filter (g₂ · ≤ y) := fun a ha ↦ by
      by_contra ha'
      have hsub' : Finset.univ.filter (g₂ · ≤ y) ⊆ Finset.univ.filter (g₁ · ≤ y) := fun b hb ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha' hb ⊢
        exact (hg₁ (le_of_not_ge fun hab ↦ ha' ((hg₂ hab).trans hb))).trans ha
      exact (Finset.sum_lt_sum_of_subset hsub' ha ha' (hpos a) fun b _ _ ↦ w.nonneg b).not_ge hle
    exact Finset.Subset.antisymm (hsub hf₁ hf₂ hsum.le) (hsub hf₂ hf₁ hsum.ge)
  funext x
  have hle (y : Y) : f₁ x ≤ y ↔ f₂ x ≤ y := by simpa using Finset.ext_iff.1 (hset y) x
  exact le_antisymm ((hle (f₂ x)).2 le_rfl) ((hle (f₁ x)).1 le_rfl)

end Semiring

end Convexity.StdSimplex
