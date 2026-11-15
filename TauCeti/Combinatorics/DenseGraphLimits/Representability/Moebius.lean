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

* isomorphism invariance together with reflection positivity makes it nonnegative.  The connection
  matrix of the fully labeled graphs on `Fin n` has entries `f(G ⊔ G')`, which by inversion is
  `Z · diag(f†) · Zᵀ` for the zeta matrix `Z(G, H) = [G ≤ H]`.  The zeta matrix is invertible, so
  this connection matrix is positive semidefinite exactly when every `f†(H)` is nonnegative;
* multiplicativity and normalization make it sum to one, since the total mass is `f` of the
  edgeless graph;
* isomorphism invariance, multiplicativity and normalization make the levels consistent: for a
  label injection `e : Fin k ↪ Fin n`, the mass `f†(G)` is the total mass of the graphs `H` on
  `Fin n` with `H.comap e = G`.  Both sides have the same sums over the supergraphs of any `F`,
  namely `f(F)` and `f(F.map e)`, and relabeling `F` into `Fin n` adjoins isolated vertices, which
  does not change `f`.

These are the facts that turn a parameter satisfying the structural conditions into a random graph
model whose upper masses `P(F ≤ ·)` are the values of `f`.

## Main definitions

* `TauCeti.DenseGraphLimits.graphParamMobius` is the Möbius transform `f†`.

## Main results

* `TauCeti.DenseGraphLimits.sum_graphParamMobius_filter_le` — Möbius inversion
  `∑_{G ≥ F} f†(G) = f(F)`;
* `TauCeti.DenseGraphLimits.eq_graphParamMobius_iff` — `f†` is the unique function with that
  property;
* `TauCeti.DenseGraphLimits.connectionMatrix_fullyLabeled` — the factorization
  `C = Z · diag(f†) · Zᵀ` of the connection matrix of the fully labeled graphs on `Fin n`, for an
  isomorphism-invariant parameter;
* `TauCeti.DenseGraphLimits.posSemidef_connectionMatrix_fullyLabeled_iff` — that connection matrix
  is positive semidefinite iff the Möbius masses at level `n` are nonnegative;
* `TauCeti.DenseGraphLimits.graphParamMobius_nonneg` — `f† ≥ 0` for an isomorphism-invariant,
  reflection-positive parameter;
* `TauCeti.DenseGraphLimits.graphParamMobius_sum_eq_one` — `∑ f† = 1` at every level for a
  multiplicative, normalized parameter;
* `TauCeti.DenseGraphLimits.graphParamMobius_sum_comap` — the Möbius consistency
  `f†(G) = ∑_{H.comap e = G} f†(H)` along every label injection `e`, for an
  isomorphism-invariant, multiplicative, normalized parameter.

The section `Examples` computes the transforms of the homomorphism densities of the constant
graphons `1` and `0`: point masses at the complete and at the edgeless graph.

## Implementation

Edge counts are `Nat.card G.edgeSet`, so the transform needs no decidability of adjacency in the
summed graphs.  The factorization, and with it nonnegativity, assumes isomorphism invariance: the
gluing of two fully labeled graphs is `G ⊔ G'` only up to the relabeling in `LabeledGraph.glue`
(`LabeledGraph.glueFullyLabeledIso`), and invariance is what identifies its value with
`f(G ⊔ G')`.  The zeta and Möbius matrices are `SimpleGraph.zetaMatrix` and
`SimpleGraph.mobiusMatrix`.

## References

* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), 933–957, Section 2 —
  the Möbius transform `f†` and its role in the proof of Theorem 2.2.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Sections 4.3 and 5.3.
-/

public section

namespace TauCeti.DenseGraphLimits

open Finset
open scoped Matrix

open Classical in
/-- The **Möbius transform** `f†` of a graph parameter over supergraphs on the same vertex set:
`f†(F) = ∑_{G ≥ F} (-1)^{e(G) - e(F)} f(G)`, the coefficients of `f` in the "contains exactly"
basis.  Edge counts are `Nat.card`, so no decidability is needed on the summed graphs. -/
noncomputable def graphParamMobius (f : GraphParam) : GraphParam := fun n F ↦
  ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) ↦ F ≤ G),
    (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) * f n G

open Classical in
/-- The defining formula of the Möbius transform. This is an explicit rewrite rule rather than a
simp lemma, so simplification can recognize the outer sum in `sum_graphParamMobius_filter_le`
before unfolding its summands. -/
theorem graphParamMobius_apply (f : GraphParam) (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius f n F =
      ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) ↦ F ≤ G),
        (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) * f n G := by
  simp only [graphParamMobius]

open Classical in
/-- **Möbius inversion.** The Möbius masses of the supergraphs of `F` add up to `f(F)`: the
signed sum over each interval `[F, H]` cancels unless `F = H`. -/
@[simp]
theorem sum_graphParamMobius_filter_le (f : GraphParam) {n : ℕ} (F : SimpleGraph (Fin n)) :
    ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) ↦ F ≤ G), graphParamMobius f n G = f n F := by
  simp_rw [graphParamMobius_apply]
  rw [Finset.sum_filter_le_sum_filter_le F fun G H ↦
    (-1 : ℝ) ^ (Nat.card H.edgeSet - Nat.card G.edgeSet) * f n H]
  have hcancel (H : SimpleGraph (Fin n)) :
      ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) ↦ F ≤ G ∧ G ≤ H),
        (-1 : ℝ) ^ (Nat.card H.edgeSet - Nat.card G.edgeSet) = if F = H then 1 else 0 := by
    simpa only [Nat.card_coe_set_eq] using
      SimpleGraph.sum_neg_one_pow_ncard_edgeSet_sub_right (R := ℝ) F H
  simp_rw [← sum_mul, hcancel, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, ite_true]

open Classical in
/-- **`f†` is characterized by Möbius inversion.** A function `g` on the graphs on `Fin n` is the
Möbius transform of `f` exactly when its masses on the supergraphs of every `F` add up to `f(F)`. -/
theorem eq_graphParamMobius_iff (f : GraphParam) {n : ℕ} (g : SimpleGraph (Fin n) → ℝ) :
    g = graphParamMobius f n ↔
      ∀ F : SimpleGraph (Fin n), ∑ G ∈ univ.filter (fun G ↦ F ≤ G), g G = f n F := by
  refine ⟨fun h F ↦ h ▸ sum_graphParamMobius_filter_le f F, fun h ↦ funext fun F ↦ ?_⟩
  simp_rw [graphParamMobius_apply, ← h, mul_sum]
  rw [Finset.sum_filter_le_sum_filter_le F fun G H ↦
    (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) * g H]
  have hcancel (H : SimpleGraph (Fin n)) :
      ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) ↦ F ≤ G ∧ G ≤ H),
        (-1 : ℝ) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) = if F = H then 1 else 0 := by
    simpa only [Nat.card_coe_set_eq] using
      SimpleGraph.sum_neg_one_pow_ncard_edgeSet_sub_left (R := ℝ) F H
  simp_rw [← sum_mul, hcancel, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, ite_true]

/-- **The Möbius masses sum to one.** For a multiplicative, normalized parameter the total mass at
every level is `f` of the edgeless graph, which is `1`. -/
theorem graphParamMobius_sum_eq_one (f : GraphParam) (hmul : IsMultiplicative f)
    (hnorm : IsNormalized f) (n : ℕ) :
    ∑ G : SimpleGraph (Fin n), graphParamMobius f n G = 1 := by
  classical
  have h := sum_graphParamMobius_filter_le f (⊥ : SimpleGraph (Fin n))
  rw [filter_true_of_mem fun G _ ↦ bot_le] at h
  convert h using 1
  exact (hmul.apply_bot hnorm n).symm

open Classical in
/-- **Möbius consistency.** For an isomorphism-invariant, multiplicative, normalized parameter, the
Möbius mass of a graph `G` on `Fin k` is the total Möbius mass of the graphs on `Fin n` whose
restriction along the label injection `e` is `G`.  Reflection positivity is not needed. -/
theorem graphParamMobius_sum_comap (f : GraphParam) (hiso : IsIsoInvariant f)
    (hmul : IsMultiplicative f) (hnorm : IsNormalized f) {k n : ℕ} (e : Fin k ↪ Fin n)
    (G : SimpleGraph (Fin k)) :
    graphParamMobius f k G =
      ∑ H ∈ univ.filter (fun H : SimpleGraph (Fin n) ↦ H.comap ⇑e = G),
        graphParamMobius f n H := by
  -- By uniqueness of the Möbius transform it suffices that the right side sums to `f(F)` over the
  -- supergraphs of every `F`; that sum is over the `H` above `F.map e`, so it is `f(F.map e)`.
  refine congrFun ((eq_graphParamMobius_iff f fun G : SimpleGraph (Fin k) ↦
    ∑ H ∈ univ.filter (fun H : SimpleGraph (Fin n) ↦ H.comap ⇑e = G),
      graphParamMobius f n H).2 fun F ↦ ?_).symm G
  simp_rw [sum_filter (s := univ) (p := fun H : SimpleGraph (Fin n) ↦ H.comap ⇑e = _)]
  rw [sum_comm]
  simp_rw [sum_ite_eq, mem_filter, mem_univ, true_and, ← SimpleGraph.map_le_iff_le_comap,
    ← sum_filter, sum_graphParamMobius_filter_le, hmul.apply_map hiso hnorm]

open Classical in
/-- **The connection-matrix factorization `C = Z · diag(f†) · Zᵀ`.** For an isomorphism-invariant
parameter, the connection matrix of the fully labeled graphs on `Fin n` has entries `f(G ⊔ G')`,
and Möbius inversion expands them as `∑_H [G ≤ H] [G' ≤ H] f†(H)`: the connection matrix is the
congruence of the diagonal matrix of Möbius masses by the zeta matrix of the lattice of graphs. -/
theorem connectionMatrix_fullyLabeled (f : GraphParam) (hf : IsIsoInvariant f) (n : ℕ) :
    connectionMatrix f (LabeledGraph.fullyLabeled (n := n)) =
      SimpleGraph.zetaMatrix (Fin n) ℝ * Matrix.diagonal (graphParamMobius f n) *
        (SimpleGraph.zetaMatrix (Fin n) ℝ)ᵀ := by
  ext G G'
  rw [connectionMatrix_apply, LabeledGraph.forgetLabels_def,
    ← hf.eq_of_iso (LabeledGraph.glueFullyLabeledIso G G'),
    ← sum_graphParamMobius_filter_le f (G ⊔ G'), sum_filter, Matrix.mul_apply]
  refine sum_congr rfl fun H _ ↦ ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply, SimpleGraph.zetaMatrix_apply,
    SimpleGraph.zetaMatrix_apply, sup_le_iff]
  by_cases hG : G ≤ H <;> by_cases hG' : G' ≤ H <;> simp [hG, hG']

/-- **Reflection positivity on the fully labeled graphs is nonnegativity of the Möbius masses.**
For an isomorphism-invariant parameter, the connection matrix of the fully labeled graphs on
`Fin n` is positive semidefinite exactly when every Möbius mass `f†(H)` of a graph on `Fin n` is
nonnegative: by `connectionMatrix_fullyLabeled` it is congruent to the diagonal matrix of Möbius
masses, and the zeta matrix is invertible. -/
theorem posSemidef_connectionMatrix_fullyLabeled_iff (f : GraphParam) (hf : IsIsoInvariant f)
    (n : ℕ) :
    (connectionMatrix f (LabeledGraph.fullyLabeled (n := n))).PosSemidef ↔
      ∀ H : SimpleGraph (Fin n), 0 ≤ graphParamMobius f n H := by
  classical
  rw [connectionMatrix_fullyLabeled f hf n, ← Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h
    -- Undo the congruence by the Möbius matrix `M`, the inverse of the zeta matrix `Z`.
    set M := SimpleGraph.mobiusMatrix (Fin n) ℝ
    set Z := SimpleGraph.zetaMatrix (Fin n) ℝ
    set D := Matrix.diagonal (graphParamMobius f n)
    have hcongr : M * (Z * D * Zᵀ) * Mᵀ = (M * Z) * D * (M * Z)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have hMZ : M * Z = 1 := SimpleGraph.mobiusMatrix_mul_zetaMatrix
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hcongr, hMZ] using
      h.mul_mul_conjTranspose_same M
  · intro h
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      h.mul_mul_conjTranspose_same (SimpleGraph.zetaMatrix (Fin n) ℝ)

/-- **Isomorphism invariance and reflection positivity make the Möbius masses nonnegative**: the
connection matrix of the fully labeled graphs on `Fin n` is positive semidefinite, which by
`posSemidef_connectionMatrix_fullyLabeled_iff` is the nonnegativity of the Möbius masses. -/
theorem graphParamMobius_nonneg (f : GraphParam) (hiso : IsIsoInvariant f)
    (hrp : IsReflectionPositive f) (n : ℕ) (F : SimpleGraph (Fin n)) :
    0 ≤ graphParamMobius f n F :=
  (posSemidef_connectionMatrix_fullyLabeled_iff f hiso n).1 (hrp.posSemidef _) F

section Examples

/-! ### The constant graphons

The homomorphism density of the constant graphon `1` is the parameter constantly `1`; that of the
constant graphon `0` is `1` on the edgeless graphs and `0` otherwise.  Their Möbius transforms are
the point masses at the complete and at the edgeless graph: the `1`-random graph is complete, and
the `0`-random graph is edgeless. -/

open Classical in
/-- The Möbius transform of the parameter constantly `1` is the point mass at the complete
graph. -/
private theorem graphParamMobius_one (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius (fun _ _ ↦ 1) n F = if F = ⊤ then 1 else 0 := by
  classical
  have h := (eq_graphParamMobius_iff (fun _ _ ↦ (1 : ℝ)) fun G : SimpleGraph (Fin n) ↦
    if G = ⊤ then 1 else 0).2 fun F ↦ by simp [sum_ite_eq', le_top]
  exact (congrFun h F).symm

open Classical in
/-- The Möbius transform of the indicator of the edgeless graphs is the point mass at the edgeless
graph. -/
private theorem graphParamMobius_ite_eq_bot (n : ℕ) (F : SimpleGraph (Fin n)) :
    graphParamMobius (fun _ G ↦ if G = ⊥ then 1 else 0) n F = if F = ⊥ then 1 else 0 := by
  classical
  have h := (eq_graphParamMobius_iff (fun _ G ↦ if G = ⊥ then (1 : ℝ) else 0)
    fun G : SimpleGraph (Fin n) ↦ if G = ⊥ then 1 else 0).2 fun F ↦ by
      simp [sum_ite_eq', le_bot_iff]
  exact (congrFun h F).symm

end Examples

end TauCeti.DenseGraphLimits
