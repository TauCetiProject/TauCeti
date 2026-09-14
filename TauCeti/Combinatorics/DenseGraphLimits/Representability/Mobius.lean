/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Representability.ConnectionMatrix
public import TauCeti.Combinatorics.SimpleGraph.EdgeCount

/-!
# The Möbius transform of a graph parameter

The **Möbius transform** `f†` of a graph parameter `f` is its expansion in the "contains exactly"
basis: `f† F` is the alternating sum of `f` over the supergraphs of `F` on the same vertex set, and
inverting that, `f F` is the total mass `f†` puts on the supergraphs of `F`.  When `f` is a
homomorphism density `t(·, W)`, so that `f F` is the probability that a `W`-random graph contains a
copy of `F` on prescribed vertices, `f† F` is the probability that the random graph is *equal* to
`F` there.

This file builds `f†` and the two laws that make that reading legitimate for an arbitrary
parameter: reflection positivity forces `f†` to be nonnegative, and multiplicativity with
normalization forces its masses at each level to sum to one.  Together they say that a
reflection-positive, multiplicative, normalized parameter determines a probability distribution on
the graphs on each finite vertex set, which is the first step from the structural conditions of the
Lovász–Szegedy representability theorem to a random graph.

## Main definitions

* `TauCeti.DenseGraphLimits.graphParamMobius` is the Möbius transform `f†`.

## Main results

* `TauCeti.DenseGraphLimits.graphParamMobius_apply` is the defining alternating sum;
* `TauCeti.DenseGraphLimits.sum_graphParamMobius` is Möbius inversion: summing `f†` over the
  supergraphs of `F` recovers `f F`;
* `TauCeti.DenseGraphLimits.graphParamMobius_sum_eq_one` — the level-`n` masses of `f†` sum to `1`
  for a multiplicative, normalized parameter;
* `TauCeti.DenseGraphLimits.graphParamMobius_nonneg` — `f†` is nonnegative for an
  isomorphism-invariant, reflection-positive parameter;
* `TauCeti.DenseGraphLimits.graphParamMobius_one` computes the transform of the constant parameter
  `1`, the point mass at the complete graph.

## Implementation

`graphParamMobius_nonneg` reads the values of `f†` off the connection matrix of the family of all
graphs on `Fin n`, each carrying the identity labelling of all of its vertices.  Gluing two such
fully labeled graphs identifies every vertex, so the glued graph is the union of the two edge sets
— but only up to the isomorphism that renames the glued vertex set, which is why isomorphism
invariance is assumed alongside reflection positivity.  The values of `f†` are then the values of
the quadratic form of that connection matrix at the vectors of Möbius signs, so positive
semidefiniteness gives them directly.

## References

* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), 933–957, Section 5 —
  the Möbius transform and the random graph attached to a reflection-positive parameter.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Chapter 6.
-/

-- Provenance: the names and signatures of the declarations below follow
-- `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.

public section

namespace TauCeti.DenseGraphLimits

open scoped Matrix

open Classical in
/-- The **Möbius transform** `f†` of a graph parameter: the alternating sum
`f† F = ∑_{G ⊇ F} (-1) ^ (e(G) - e(F)) · f G` over the supergraphs of `F` on the same vertex set.
It expresses `f` in the basis of "contains exactly" events. -/
noncomputable def graphParamMobius (f : GraphParam) : GraphParam := fun n F =>
  ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => F ≤ G),
    (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) * f n G

open Classical in
/-- The defining alternating sum of the Möbius transform. -/
theorem graphParamMobius_apply (f : GraphParam) (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius f n F
      = ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => F ≤ G),
          (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) * f n G := (rfl)

open Classical in
/-- **Möbius inversion.**  The value of `f` at `F` is the total mass its Möbius transform puts on
the supergraphs of `F`. -/
theorem sum_graphParamMobius (f : GraphParam) (n : ℕ) (F : SimpleGraph (Fin n)) :
    ∑ K ∈ Finset.univ.filter (fun K : SimpleGraph (Fin n) => F ≤ K), graphParamMobius f n K
      = f n F := by
  have hcomm : ∑ K ∈ Finset.univ.filter (fun K : SimpleGraph (Fin n) => F ≤ K),
      ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => K ≤ G),
        (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card K.edgeSet) * f n G
      = ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => F ≤ G),
          ∑ K ∈ Finset.univ.filter (fun K : SimpleGraph (Fin n) => F ≤ K ∧ K ≤ G),
            (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card K.edgeSet) * f n G :=
    Finset.sum_comm' (by
      intro K G
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.1.trans h.2⟩, fun h => ⟨h.1.1, h.1.2⟩⟩)
  have hinner : ∀ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => F ≤ G),
      (∑ K ∈ Finset.univ.filter (fun K : SimpleGraph (Fin n) => F ≤ K ∧ K ≤ G),
        (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card K.edgeSet) * f n G)
      = (if F = G then (1 : ℝ) else 0) * f n G := by
    intro G _
    rw [← Finset.sum_mul, Finset.sum_congr rfl fun K hK =>
      SimpleGraph.neg_one_pow_card_edgeSet_sub (R := ℝ) (Finset.mem_filter.1 hK).2.2,
      ← Finset.mul_sum, SimpleGraph.sum_neg_one_pow_card_edgeSet]
    split_ifs with h
    · subst h
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    · rw [mul_zero, zero_mul]
  have hFmem : F ∈ Finset.univ.filter (fun K : SimpleGraph (Fin n) => F ≤ K) := by simp
  simp only [graphParamMobius_apply]
  rw [hcomm, Finset.sum_congr rfl hinner]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single_of_mem F hFmem fun b _ hb => by simp [Ne.symm hb]]
  simp

open Classical in
/-- **The Möbius masses at each level sum to one.**  With `graphParamMobius_nonneg` this makes the
transform of a multiplicative, normalized, reflection-positive parameter a probability mass
function on the graphs on `Fin n`. -/
theorem graphParamMobius_sum_eq_one (f : GraphParam) (h₂ : IsMultiplicative f)
    (h₃ : IsNormalized f) (n : ℕ) :
    ∑ G : SimpleGraph (Fin n), graphParamMobius f n G = 1 := by
  have huniv : (Finset.univ.filter fun K : SimpleGraph (Fin n) => (⊥ : SimpleGraph (Fin n)) ≤ K)
      = Finset.univ := by
    ext K
    simp
  rw [← huniv, sum_graphParamMobius f n ⊥, h₂.apply_bot h₃ n]

open Classical in
/-- The quadratic form of `f` on gluings, expanded in the Möbius basis: the coefficient of `f† K`
is the square of the total weight below `K`. -/
private theorem sum_sum_mul_apply_sup (f : GraphParam) (n : ℕ) (x : SimpleGraph (Fin n) → ℝ) :
    ∑ G, ∑ H, x G * x H * f n (G ⊔ H)
      = ∑ K, (∑ G, x G * (if G ≤ K then (1 : ℝ) else 0))
          * (∑ H, x H * (if H ≤ K then (1 : ℝ) else 0)) * graphParamMobius f n K := by
  have hexp : ∀ G H : SimpleGraph (Fin n), f n (G ⊔ H)
      = ∑ K, (if G ≤ K then (1 : ℝ) else 0) * (if H ≤ K then (1 : ℝ) else 0)
          * graphParamMobius f n K := by
    intro G H
    rw [← sum_graphParamMobius f n (G ⊔ H), Finset.sum_filter]
    refine Finset.sum_congr rfl fun K _ => ?_
    by_cases hG : G ≤ K <;> by_cases hH : H ≤ K <;> simp [hG, hH, sup_le_iff]
  calc ∑ G, ∑ H, x G * x H * f n (G ⊔ H)
      = ∑ G, ∑ H, ∑ K, (x G * (if G ≤ K then (1 : ℝ) else 0))
          * (x H * (if H ≤ K then (1 : ℝ) else 0)) * graphParamMobius f n K := by
        refine Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun H _ => ?_
        rw [hexp, Finset.mul_sum]
        exact Finset.sum_congr rfl fun K _ => by ring
    _ = ∑ G, ∑ K, ∑ H, (x G * (if G ≤ K then (1 : ℝ) else 0))
          * (x H * (if H ≤ K then (1 : ℝ) else 0)) * graphParamMobius f n K :=
        Finset.sum_congr rfl fun G _ => Finset.sum_comm
    _ = ∑ K, ∑ G, ∑ H, (x G * (if G ≤ K then (1 : ℝ) else 0))
          * (x H * (if H ≤ K then (1 : ℝ) else 0)) * graphParamMobius f n K := Finset.sum_comm
    _ = ∑ K, (∑ G, x G * (if G ≤ K then (1 : ℝ) else 0))
          * (∑ H, x H * (if H ≤ K then (1 : ℝ) else 0)) * graphParamMobius f n K := by
        refine Finset.sum_congr rfl fun K _ => ?_
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun G _ => by rw [Finset.sum_mul]

open Classical in
/-- The Möbius signs of the supergraphs of `F` inside `K` add up to `1` when `F = K`. -/
private theorem sum_mobiusSign_indicator (n : ℕ) (F K : SimpleGraph (Fin n)) :
    ∑ G, (if F ≤ G then (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) else 0)
        * (if G ≤ K then (1 : ℝ) else 0) = if F = K then (1 : ℝ) else 0 := by
  have h1 : ∀ G : SimpleGraph (Fin n),
      (if F ≤ G then (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) else 0)
          * (if G ≤ K then (1 : ℝ) else 0)
        = if F ≤ G ∧ G ≤ K then
            (-1 : ℝ) ^ Nat.card G.edgeSet * (-1 : ℝ) ^ Nat.card F.edgeSet else 0 := by
    intro G
    by_cases hF : F ≤ G
    · rw [SimpleGraph.neg_one_pow_card_edgeSet_sub (R := ℝ) hF]
      by_cases hK : G ≤ K <;> simp [hF, hK]
    · simp [hF]
  rw [Finset.sum_congr rfl fun G _ => h1 G, ← Finset.sum_filter, ← Finset.sum_mul,
    SimpleGraph.sum_neg_one_pow_card_edgeSet]
  split_ifs with h
  · rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  · rw [zero_mul]

/-- The `n`-labeled graph on `Fin n` whose every vertex carries its own label. -/
private def fullyLabeled {n : ℕ} (G : SimpleGraph (Fin n)) : LabeledGraph n :=
  ⟨n, G, id, Function.injective_id⟩

/-- Both factors of a gluing of fully labeled graphs enter through the same vertex map, since every
vertex carries a label. -/
private theorem glueInl_eq_glueInr_fullyLabeled {n : ℕ} (G H : SimpleGraph (Fin n)) :
    ⇑((fullyLabeled G).glueInl (fullyLabeled H))
      = ⇑((fullyLabeled G).glueInr (fullyLabeled H)) := by
  have h1 : ((fullyLabeled G).glue (fullyLabeled H)).label
      = ⇑((fullyLabeled G).glueInl (fullyLabeled H)) := by
    simpa [fullyLabeled] using LabeledGraph.glueInl_label (fullyLabeled G) (fullyLabeled H)
  have h2 : ((fullyLabeled G).glue (fullyLabeled H)).label
      = ⇑((fullyLabeled G).glueInr (fullyLabeled H)) := by
    simpa [fullyLabeled] using LabeledGraph.glueInr_label (fullyLabeled G) (fullyLabeled H)
  exact h1.symm.trans h2

/-- Gluing two fully labeled graphs on `Fin n` identifies all their vertices, so the result is the
union of the two edge sets, read along the left inclusion. -/
private noncomputable def glueFullyLabeledIso {n : ℕ} (G H : SimpleGraph (Fin n)) :
    (G ⊔ H) ≃g ((fullyLabeled G).glue (fullyLabeled H)).graph where
  toEquiv := Equiv.ofBijective ((fullyLabeled G).glueInl (fullyLabeled H))
    ⟨((fullyLabeled G).glueInl (fullyLabeled H)).injective, by
      intro v
      rcases LabeledGraph.glue_surjective (fullyLabeled G) (fullyLabeled H) v with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact ⟨a, ha.symm⟩
      · exact ⟨b, by rw [hb, ← congrFun (glueInl_eq_glueInr_fullyLabeled G H) b]⟩⟩
  map_rel_iff' := by
    intro a b
    refine (LabeledGraph.glue_adj_inl (fullyLabeled G) (fullyLabeled H) a b).trans ?_
    simp [fullyLabeled, SimpleGraph.sup_adj]

open Classical in
/-- **Reflection positivity makes the Möbius transform nonnegative.**  The values of `f†` on the
graphs on `Fin n` are values of the quadratic form of the connection matrix of the fully labeled
graphs on `Fin n`, which reflection positivity makes positive semidefinite. -/
theorem graphParamMobius_nonneg (f : GraphParam) (h₁ : IsIsoInvariant f)
    (h₄ : IsReflectionPositive f) (n : ℕ) (F : SimpleGraph (Fin n)) :
    0 ≤ graphParamMobius f n F := by
  have hentry : ∀ G H : SimpleGraph (Fin n),
      connectionMatrix f (fullyLabeled (n := n)) G H = f n (G ⊔ H) := fun G H => by
    rw [connectionMatrix_apply, LabeledGraph.forgetLabels_def]
    exact (h₁.eq_of_iso (glueFullyLabeledIso G H)).symm
  set x : SimpleGraph (Fin n) → ℝ :=
    fun G => if F ≤ G then (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) else 0 with hx
  have hquad := (h₄.posSemidef (fullyLabeled (n := n))).dotProduct_mulVec_nonneg x
  have hval : star x ⬝ᵥ (connectionMatrix f (fullyLabeled (n := n)) *ᵥ x)
      = graphParamMobius f n F := by
    have h0 : star x ⬝ᵥ (connectionMatrix f (fullyLabeled (n := n)) *ᵥ x)
        = ∑ G, ∑ H, x G * x H * f n (G ⊔ H) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, hentry, Finset.mul_sum]
      exact Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun H _ => by ring
    rw [h0, sum_sum_mul_apply_sup]
    simp only [hx, sum_mobiusSign_indicator]
    rw [Finset.sum_eq_single_of_mem F (Finset.mem_univ F) fun b _ hb => by simp [Ne.symm hb]]
    simp
  rwa [hval] at hquad

/-! ### The constant parameter

The parameter constantly `1` is the homomorphism density `t(·, W)` of the constant graphon `W ≡ 1`,
whose random graph on any vertex set is complete.  Its Möbius transform is the corresponding point
mass, a check that `graphParamMobius` computes the "contains exactly" probabilities and not merely
some alternating sum. -/

open Classical in
/-- The Möbius transform of the constant parameter `1` is the point mass at the complete graph. -/
theorem graphParamMobius_one (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius (fun _ _ => (1 : ℝ)) n F = if F = ⊤ then 1 else 0 := by
  have hmem : ∀ G : SimpleGraph (Fin n), (F ≤ G ∧ G ≤ ⊤) ↔ F ≤ G := fun G => by simp
  simp only [graphParamMobius_apply, mul_one]
  rw [Finset.sum_congr (Finset.filter_congr fun G _ => (hmem G).symm)
      fun G hG => SimpleGraph.neg_one_pow_card_edgeSet_sub (R := ℝ) (Finset.mem_filter.1 hG).2.1,
    ← Finset.sum_mul, SimpleGraph.sum_neg_one_pow_card_edgeSet]
  split_ifs with h
  · subst h
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  · rw [zero_mul]

end TauCeti.DenseGraphLimits
