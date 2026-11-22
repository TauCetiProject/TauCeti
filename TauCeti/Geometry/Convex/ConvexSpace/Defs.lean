/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import TauCeti.Algebra.BigOperators.Finset.PartialSum

/-!
# Faces of the standard simplex

Complements to Mathlib's `Convexity.StdSimplex`, mostly about the maps `StdSimplex.map f`.  A point
is determined by its weight function (`StdSimplex.toFun_comp_weights_injective`), and
`StdSimplex.extendWeights p` inverts the weight function on its range, sending every other
function to the fallback point `p`.  An arbitrary map adds weights over its fibres.  An injective
map embeds a standard simplex as a face of a larger
one and keeps the weights of a point, so it is injective; a point supported on its range comes from
the smaller simplex (`StdSimplex.comap`).  For `f = j.succAbove` its image is the
facet on which the `j`-th weight vanishes; for the last vertex this facet is the smaller simplex
with a zero last weight appended.  A function taking a constant value on every facet
takes that value wherever some weight vanishes.  Two facets, opposite `j < k`, meet in the
codimension-two face opposite both: a common point of the two facets comes from that face through
both composites of face maps, the two sides of the simplicial identity
`SimplexCategory.δ_comp_δ`.

The prefix sums `TauCeti.prefixSum N x.weights` of the weights of a point `x` of
`StdSimplex R (Fin n)` lie between `0` and `1`. Scalar pushforward `StdSimplex.mapRange` along a
semiring homomorphism sending nonnegative elements to nonnegative elements applies the
homomorphism to each weight and commutes with `StdSimplex.map`.
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

/-- A point of `StdSimplex R Y` whose weights are supported on the range of an injective map
`f : X → Y`, pulled back to `StdSimplex R X`: a right inverse of `StdSimplex.map f` on its range
(`StdSimplex.map_comap`), and a left inverse of it (`StdSimplex.comap_map`). -/
noncomputable def comap {f : X → Y} (hf : f.Injective) (y : StdSimplex R Y)
    (h : ↑y.weights.support ⊆ Set.range f) : StdSimplex R X where
  weights := Finsupp.comapDomain f y.weights hf.injOn
  nonneg a := by simpa using y.nonneg (f a)
  total := by
    have := y.total
    rwa [← Finsupp.mapDomain_comapDomain f hf y.weights h,
      Finsupp.sum_mapDomain_index (by simp) (by simp)] at this

/-- The weights of a pulled back point are the pulled back weights. -/
theorem weights_comap {f : X → Y} (hf : f.Injective) (y : StdSimplex R Y)
    (h : ↑y.weights.support ⊆ Set.range f) :
    (comap hf y h).weights = Finsupp.comapDomain f y.weights hf.injOn :=
  (rfl)

/-- The weight of a pulled back point at `a` is the weight of the point at `f a`. -/
@[simp]
theorem weights_comap_apply {f : X → Y} (hf : f.Injective) (y : StdSimplex R Y)
    (h : ↑y.weights.support ⊆ Set.range f) (a : X) :
    (comap hf y h).weights a = y.weights (f a) := by
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

/-- Sums of the weights of a mapped standard simplex over a set are sums of the weights over its
preimage. -/
theorem sum_filter_weights_map [Fintype X] [Fintype Y] (f : X → Y) (x : StdSimplex R X)
    (P : Y → Prop) [DecidablePred P] :
    ∑ y ∈ Finset.univ.filter P, (x.map f).weights y =
      ∑ a ∈ Finset.univ.filter (fun a ↦ P (f a)), x.weights a := by
  classical
  -- Sum the fibre sums of `weights_map_apply` over the fibres above `P`.
  simp_rw [weights_map_apply]
  simpa using Finset.sum_fiberwise_eq_sum_filter Finset.univ (Finset.univ.filter P) f x.weights

/-- Pulling back a point along an injective map whose range contains its support, and then mapping
forward again, recovers the point. -/
@[simp]
theorem map_comap {f : X → Y} (hf : f.Injective) (y : StdSimplex R Y)
    (h : ↑y.weights.support ⊆ Set.range f) : (comap hf y h).map f = y := by
  rw [← weights_inj, weights_map, weights_comap]
  exact Finsupp.mapDomain_comapDomain f hf y.weights h

/-- Mapping a point forward along an injective map and pulling it back again recovers the
point. -/
@[simp]
theorem comap_map {f : X → Y} (hf : f.Injective) (x : StdSimplex R X)
    (h : ↑(x.map f).weights.support ⊆ Set.range f) : comap hf (x.map f) h = x := by
  ext a
  rw [weights_comap_apply, weights_map_apply_of_injective hf]

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

variable {R S T X Y : Type*} [PartialOrder R] [Semiring R] [PartialOrder S] [Semiring S]
  [PartialOrder T] [Semiring T]

/-- Push a point of a standard simplex forward along a semiring homomorphism on its weights which
sends nonnegative elements to nonnegative elements, such as casting rational barycentric
coordinates into an ordered field. -/
noncomputable def mapRange (f : R →+* S) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (w : StdSimplex R X) :
    StdSimplex S X where
  weights := w.weights.mapRange f (map_zero f)
  nonneg x := by simpa using hf _ (w.weights_nonneg x)
  total := by
    rw [Finsupp.sum_mapRange_index (by simp), ← map_finsuppSum f w.weights fun _ r ↦ r,
      w.total, map_one]

/-- Scalar pushforward applies `Finsupp.mapRange` to the weight vector. -/
theorem weights_mapRange (f : R →+* S) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (w : StdSimplex R X) :
    (w.mapRange f hf).weights = w.weights.mapRange f (map_zero f) :=
  (rfl)

/-- Scalar pushforward applies the homomorphism to each weight. -/
@[simp]
theorem weights_mapRange_apply (f : R →+* S) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (w : StdSimplex R X)
    (x : X) :
    (w.mapRange f hf).weights x = f (w.weights x) := by
  rw [weights_mapRange, Finsupp.mapRange_apply]

/-- Scalar pushforward along an injective homomorphism is injective. -/
theorem mapRange_injective {f : R →+* S} (hf : ∀ r, 0 ≤ r → 0 ≤ f r)
    (hfinj : Function.Injective f) :
    Function.Injective (mapRange (X := X) f hf) := fun _ _ h ↦
  ext <| Finsupp.mapRange_injective _ (map_zero f) hfinj congr(($h).weights)

/-- Scalar pushforward along an injective homomorphism preserves the support of weights. -/
@[simp]
theorem support_weights_mapRange {f : R →+* S} (hf : ∀ r, 0 ≤ r → 0 ≤ f r)
    (hfinj : Function.Injective f) (w : StdSimplex R X) :
    (w.mapRange f hf).weights.support = w.weights.support :=
  Finsupp.support_mapRange_of_injective (map_zero f) _ hfinj

/-- Scalar pushforward sends each vertex point mass to the corresponding vertex point mass. -/
@[simp]
theorem mapRange_single [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (f : R →+* S) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (x : X) :
    (single x).mapRange f hf = single x := by
  ext y
  by_cases h : x = y <;> simp [h]

/-- Scalar pushforward commutes with pushing vertices forward along a map. -/
theorem mapRange_map [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (f : R →+* S) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (g : X → Y) (w : StdSimplex R X) :
    (w.map g).mapRange f hf = (w.mapRange f hf).map g :=
  StdSimplex.ext (Finsupp.mapDomain_mapRange g w.weights f (map_zero f) (map_add f)).symm

/-- Scalar pushforward along the identity homomorphism is the identity. -/
@[simp]
theorem mapRange_id (w : StdSimplex R X) : w.mapRange (RingHom.id R) (fun _ ↦ id) = w := by
  ext x
  simp

/-- Scalar pushforward preserves composition of semiring homomorphisms. -/
theorem mapRange_comp (g : S →+* T) (hg : ∀ s, 0 ≤ s → 0 ≤ g s) (f : R →+* S)
    (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (w : StdSimplex R X) :
    (w.mapRange f hf).mapRange g hg = w.mapRange (g.comp f) (fun r hr ↦ hg _ (hf r hr)) := by
  ext x
  simp

end MapRange

end Convexity.StdSimplex
