/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Representability.ConnectionMatrix
public import TauCeti.Combinatorics.SimpleGraph.Moebius

/-!
# The Möbius transform of a graph parameter

For a graph parameter `f` and a graph `F` on `Fin n`, the **Möbius transform**
`f†(F) = ∑_{G ≥ F} (-1)^{e(G) - e(F)} f(G)` is the coefficient of `F` when `f`, restricted to the
graphs on `Fin n`, is expanded in the "contains exactly" basis: Möbius inversion over the Boolean
lattice of graphs on `Fin n` says `f(F) = ∑_{G ≥ F} f†(G)`, and `f†` is the only function with that
property.  For the homomorphism density `f = t(·, W)` of a graphon, `f†(F)` is classically the
probability that the `W`-random graph on `n` vertices is exactly `F`; this file does not use that
interpretation.

For an arbitrary parameter, the structural conditions of the Lovász–Szegedy representability
theorem make `f†` a probability mass function at each level:

* reflection positivity makes it nonnegative.  The connection matrix of the fully labeled graphs
  on `Fin n` has entries `f(G ⊔ G')`, which by inversion is `Z · diag(f†) · Zᵀ` for the zeta
  matrix `Z(G, H) = [G ≤ H]`; pairing it with the row of `Z⁻¹` at `F` returns `f†(F)`;
* multiplicativity and normalization make it sum to one, since the total mass is `f` of the
  edgeless graph.

This is the first step from a parameter satisfying the structural conditions towards a random
graph model whose upper masses `P(F ≤ ·)` are the values of `f`.

## Main definitions

* `TauCeti.DenseGraphLimits.graphParamMobius` is the Möbius transform `f†`.

## Main results

* `TauCeti.DenseGraphLimits.sum_graphParamMobius_filter_le` — Möbius inversion
  `∑_{G ≥ F} f†(G) = f(F)`;
* `TauCeti.DenseGraphLimits.eq_graphParamMobius_iff` — `f†` is the unique function with that
  property;
* `TauCeti.DenseGraphLimits.graphParamMobius_nonneg` — `f† ≥ 0` for an isomorphism-invariant,
  reflection-positive parameter;
* `TauCeti.DenseGraphLimits.graphParamMobius_sum_eq_one` — `∑ f† = 1` at every level for a
  multiplicative, normalized parameter.

The section `Examples` computes the transforms of the homomorphism densities of the constant
graphons `1` and `0`: point masses at the complete and at the edgeless graph.

## Implementation

Edge counts are `Nat.card G.edgeSet`, so the transform needs no decidability of adjacency in the
summed graphs.  Nonnegativity assumes isomorphism invariance: the gluing of two fully labeled
graphs is specified only up to the relabeling in `LabeledGraph.glue`, and invariance is what
identifies its value with `f(G ⊔ G')`.

## References

* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), 933–957, Section 2 —
  the Möbius transform `f†` and its role in the proof of Theorem 2.2.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Sections 4.3 and 5.3.
-/

-- Provenance: the names and signatures of the declarations below follow
-- `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.

public section

namespace TauCeti.DenseGraphLimits

open Finset

open Classical in
/-- The **Möbius transform** `f†` of a graph parameter over supergraphs on the same vertex set:
`f†(F) = ∑_{G ≥ F} (-1)^{e(G) - e(F)} f(G)`, the coefficients of `f` in the "contains exactly"
basis.  Edge counts are `Nat.card`, so no decidability is needed on the summed graphs. -/
noncomputable def graphParamMobius (f : GraphParam) : GraphParam := fun n F =>
  ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) => F ≤ G),
    (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) * f n G

open Classical in
/-- The defining formula of the Möbius transform. -/
theorem graphParamMobius_apply (f : GraphParam) (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius f n F =
      ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) => F ≤ G),
        (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) * f n G := by
  simp only [graphParamMobius]

open Classical in
/-- A double sum over a chain `F ≤ G ≤ H` of graphs, summed first over `G ≥ F` and then over
`H ≥ G`, is the sum over `H` of the sum over the interval `[F, H]`. -/
private theorem sum_filter_le_sum_filter_le {n : ℕ} (F : SimpleGraph (Fin n))
    (φ : SimpleGraph (Fin n) → SimpleGraph (Fin n) → ℝ) :
    ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) => F ≤ G),
        ∑ H ∈ univ.filter (fun H : SimpleGraph (Fin n) => G ≤ H), φ G H =
      ∑ H, ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) => F ≤ G ∧ G ≤ H), φ G H := by
  calc _ = ∑ G, ∑ H, if F ≤ G ∧ G ≤ H then φ G H else 0 := by
        rw [sum_filter]
        refine sum_congr rfl fun G _ => ?_
        by_cases h : F ≤ G <;> simp [h, sum_filter]
    _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun H _ => (sum_filter _ _).symm

open Classical in
/-- **Möbius inversion.** The Möbius masses of the supergraphs of `F` add up to `f(F)`: the
signed sum over each interval `[F, H]` cancels unless `F = H`. -/
theorem sum_graphParamMobius_filter_le (f : GraphParam) {n : ℕ} (F : SimpleGraph (Fin n)) :
    ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) => F ≤ G), graphParamMobius f n G = f n F := by
  simp_rw [graphParamMobius_apply]
  rw [sum_filter_le_sum_filter_le F fun G H =>
    (-1 : ℝ) ^ (Nat.card H.edgeSet - Nat.card G.edgeSet) * f n H]
  simp_rw [← sum_mul, SimpleGraph.sum_neg_one_pow_card_edgeSet_sub_right, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, ite_true]

open Classical in
/-- **`f†` is characterized by Möbius inversion.** A function `g` on the graphs on `Fin n` is the
Möbius transform of `f` exactly when its masses on the supergraphs of every `F` add up to `f(F)`. -/
theorem eq_graphParamMobius_iff (f : GraphParam) {n : ℕ} (g : SimpleGraph (Fin n) → ℝ) :
    g = graphParamMobius f n ↔
      ∀ F : SimpleGraph (Fin n), ∑ G ∈ univ.filter (fun G => F ≤ G), g G = f n F := by
  refine ⟨fun h F => h ▸ sum_graphParamMobius_filter_le f F, fun h => funext fun F => ?_⟩
  simp_rw [graphParamMobius_apply, ← h, mul_sum]
  rw [sum_filter_le_sum_filter_le F fun G H =>
    (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) * g H]
  simp_rw [← sum_mul, SimpleGraph.sum_neg_one_pow_card_edgeSet_sub_left, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, ite_true]

/-- **The Möbius masses sum to one.** For a multiplicative, normalized parameter the total mass at
every level is `f` of the edgeless graph, which is `1`. -/
theorem graphParamMobius_sum_eq_one (f : GraphParam) (hmul : IsMultiplicative f)
    (hnorm : IsNormalized f) (n : ℕ) :
    ∑ G : SimpleGraph (Fin n), graphParamMobius f n G = 1 := by
  classical
  have h := sum_graphParamMobius_filter_le f (⊥ : SimpleGraph (Fin n))
  rw [filter_true_of_mem fun G _ => bot_le] at h
  convert h using 1
  exact (hmul.apply_bot hnorm n).symm

/-- The graph `G` on `Fin n` with every vertex labeled, by its own index. -/
private def fullyLabeled {n : ℕ} (G : SimpleGraph (Fin n)) : LabeledGraph n where
  n := n
  graph := G
  label := id
  label_injective := Function.injective_id

/-- Gluing two fully labeled graphs along their labels overlays them: for an isomorphism-invariant
parameter the connection-matrix entry is `f(G ⊔ G')`. -/
private theorem apply_glue_fullyLabeled {f : GraphParam} (hf : IsIsoInvariant f) {n : ℕ}
    (G G' : SimpleGraph (Fin n)) :
    f ((fullyLabeled G).glue (fullyLabeled G')).n ((fullyLabeled G).glue (fullyLabeled G')).graph
      = f n (G ⊔ G') := by
  set A := fullyLabeled G
  set B := fullyLabeled G'
  -- Every vertex of `B` is labeled, so the right side of the gluing lands inside the left side.
  have hbij : Function.Bijective (A.glueInl B) := ⟨(A.glueInl B).injective, fun v => by
    obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := A.glue_surjective B v
    · exact ⟨a, rfl⟩
    · exact ⟨b, (A.glueInl_eq_glueInr_iff B b b).2 ⟨b, rfl, rfl⟩⟩⟩
  refine (hf.eq_of_iso
    { toEquiv := Equiv.ofBijective _ hbij
      map_rel_iff' := fun {a b} => ?_ }).symm
  rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply, LabeledGraph.glue_adj_inl]
  -- `A` and `B` are `G` and `G'` on `Fin n` labeled by the identity, so up to unfolding
  -- `fullyLabeled` the right-hand disjunct is `G'.Adj a b` and the whole is `(G ⊔ G').Adj a b`.
  exact or_congr_right ⟨fun ⟨i, j, hi, hj, h⟩ => by rw [hi, hj]; exact h,
    fun h => ⟨a, b, rfl, rfl, h⟩⟩

/-- **Reflection positivity makes the Möbius masses nonnegative.** The connection matrix of the
fully labeled graphs on `Fin n` has entries `f(G ⊔ G') = ∑_H [G ≤ H] [G' ≤ H] f†(H)`, and its
quadratic form at the signed indicator `G ↦ [F ≤ G] (-1)^{e(G) - e(F)}` is `f†(F)`. -/
theorem graphParamMobius_nonneg (f : GraphParam) (hiso : IsIsoInvariant f)
    (hrp : IsReflectionPositive f) (n : ℕ) (F : SimpleGraph (Fin n)) :
    0 ≤ graphParamMobius f n F := by
  classical
  let z : SimpleGraph (Fin n) → SimpleGraph (Fin n) → ℝ := fun G H => if G ≤ H then 1 else 0
  let x : SimpleGraph (Fin n) → ℝ := fun G =>
    if F ≤ G then (-1) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) else 0
  -- The connection matrix factors through the zeta function of the lattice of graphs.
  have hM : ∀ G G', connectionMatrix f fullyLabeled G G' =
      ∑ H, z G H * z G' H * graphParamMobius f n H := fun G G' => by
    rw [connectionMatrix_apply, LabeledGraph.forgetLabels_def, apply_glue_fullyLabeled hiso,
      ← sum_graphParamMobius_filter_le f (G ⊔ G'), sum_filter]
    refine sum_congr rfl fun H _ => ?_
    by_cases hG : G ≤ H <;> by_cases hG' : G' ≤ H <;> simp [z, hG, hG']
  -- The signed indicator of `F` is the row of the inverse zeta matrix at `F`.
  have hx : ∀ H, ∑ G, x G * z G H = if F = H then 1 else 0 := fun H => by
    rw [← SimpleGraph.sum_neg_one_pow_card_edgeSet_sub_left (R := ℝ) F H, sum_filter]
    refine sum_congr rfl fun G _ => ?_
    by_cases hF : F ≤ G <;> by_cases hH : G ≤ H <;> simp [x, z, hF, hH]
  have h := (hrp.posSemidef fullyLabeled).dotProduct_mulVec_nonneg x
  refine h.trans_eq (Eq.symm ?_)
  simp only [star_trivial, dotProduct, Matrix.mulVec, hM]
  calc graphParamMobius f n F
      = ∑ H, (∑ G, x G * z G H) * (∑ G', x G' * z G' H) * graphParamMobius f n H := by
        simp_rw [hx]
        simp
    _ = _ := by
        simp_rw [sum_mul_sum, sum_mul, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun G _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun G' _ => sum_congr rfl fun H _ => by ring

section Examples

/-! ### The constant graphons

The homomorphism density of the constant graphon `1` is the parameter constantly `1`; that of the
constant graphon `0` is `1` on the edgeless graphs and `0` otherwise.  Their Möbius transforms are
the point masses at the complete and at the edgeless graph: the `1`-random graph is complete, and
the `0`-random graph is edgeless. -/

open Classical in
/-- The Möbius transform of the parameter constantly `1` is the point mass at the complete
graph. -/
theorem graphParamMobius_one (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius (fun _ _ => 1) n F = if F = ⊤ then 1 else 0 := by
  classical
  have h := (eq_graphParamMobius_iff (fun _ _ => (1 : ℝ)) fun G : SimpleGraph (Fin n) =>
    if G = ⊤ then 1 else 0).2 fun F => by simp [sum_ite_eq', le_top]
  exact (congrFun h F).symm

open Classical in
/-- The Möbius transform of the indicator of the edgeless graphs is the point mass at the edgeless
graph. -/
theorem graphParamMobius_ite_eq_bot (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius (fun _ G => if G = ⊥ then 1 else 0) n F = if F = ⊥ then 1 else 0 := by
  classical
  have h := (eq_graphParamMobius_iff (fun _ G => if G = ⊥ then (1 : ℝ) else 0)
    fun G : SimpleGraph (Fin n) => if G = ⊥ then 1 else 0).2 fun F => by
      simp [sum_ite_eq', le_bot_iff]
  exact (congrFun h F).symm

end Examples

end TauCeti.DenseGraphLimits
