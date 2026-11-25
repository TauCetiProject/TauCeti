/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Seminorm

/-!
# Changing the family of the word seminorms

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V`, and let
`P^X_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖` be the word seminorm of order `k` along a finite family
`X` of left-invariant derivations (`ContRepresentation.wordSeminorm`).

The comparison is proved once for the word seminorms `P^D_k` along families `D` of operators on the
smooth vectors (`ContRepresentation.endWordSeminorm`), with coefficients in `𝕜`. With the recursion
`P^D_{k+1}(v) = ‖v‖ + ∑ i, P^D_k(D_i v)` (`ContRepresentation.endWordSeminorm_succ`) and the
derivative estimate `P^D_k(A v) ≤ (∑ i, ‖c i‖) P^D_{k+1}(v)` for `A = ∑ i, c i • D i`, induction on
`k` compares the word seminorms along two families: if `D' j = ∑ i, c j i • D i` for every `j`, then
`P^{D'}_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^D_k`. For `D i = dπ(X_i)` and real coefficients this says:
if `Y j = ∑ i, c j i • X i` for every `j`, then `P^Y_k ≤ (1 + ∑ j, ∑ i, |c j i|)^k P^X_k`. Every
finite family is a real combination of a real basis `b` of the Lie algebra, so its word seminorms
are bounded by those along `b` (`Seminorm.IsBounded`). For two bases this applies in both
directions: the two families of word seminorms bound each other, so any topology induced by the word
seminorms (for instance through `WithSeminorms.congr`) does not depend on the basis.

## Main results

* `ContRepresentation.endWordSeminorm_le_of_eq_sum`: the comparison for the word seminorms along
  families of operators (`ContRepresentation.endWordSeminorm`): if `D' j = ∑ i, c j i • D i`, then
  `P^{D'}_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^D_k`.
* `ContRepresentation.wordSeminorm_le_of_eq_sum`: if `Y j = ∑ i, c j i • X i`, then
  `P^Y_k ≤ (1 + ∑ j, ∑ i, |c j i|)^k P^X_k`.
* `ContRepresentation.wordSeminorm_le_basis`: the comparison of any finite family with a real
  basis.
* `ContRepresentation.isBounded_wordSeminorm_basis`: the word seminorms along any finite family
  are bounded by those along a real basis, as families of seminorms (`Seminorm.IsBounded`).

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.5.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

section EndWordSeminorm

omit [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

/-- **Comparison of the word seminorms along two families of operators.** If
`D' j = ∑ i, c j i • D i` for every `j`, then `P^{D'}_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^D_k`. -/
theorem endWordSeminorm_le_of_eq_sum (D : ι → Module.End 𝕜 (lieSmoothVectors I π))
    {D' : κ → Module.End 𝕜 (lieSmoothVectors I π)} (c : κ → ι → 𝕜)
    (hD : ∀ j, D' j = ∑ i, c j i • D i) (k : ℕ) (v : lieSmoothVectors I π) :
    endWordSeminorm D' k v ≤ (1 + ∑ j, ∑ i, ‖c j i‖) ^ k * endWordSeminorm D k v := by
  set S := ∑ j, ∑ i, ‖c j i‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    have hC : 1 ≤ (1 + S) ^ k := one_le_pow₀ (le_add_of_nonneg_right hS)
    have hv : ‖(v : V)‖ ≤ (1 + S) ^ k * endWordSeminorm D (k + 1) v := by
      rw [← endWordSeminorm_zero D]
      exact (endWordSeminorm_mono D (Nat.zero_le _) v).trans
        (le_mul_of_one_le_left (apply_nonneg _ _) hC)
    have hsum : ∑ j, endWordSeminorm D' k (D' j v) ≤
        (1 + S) ^ k * (S * endWordSeminorm D (k + 1) v) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ ↦ (ih _).trans ?_
      exact mul_le_mul_of_nonneg_left
        (endWordSeminorm_apply_le_of_eq_sum D k (c j) (hD j) v) (pow_nonneg (by positivity) _)
    rw [endWordSeminorm_succ]
    calc ‖(v : V)‖ + ∑ j, endWordSeminorm D' k (D' j v)
      _ ≤ (1 + S) ^ k * endWordSeminorm D (k + 1) v +
          (1 + S) ^ k * (S * endWordSeminorm D (k + 1) v) := add_le_add hv hsum
      _ = (1 + S) ^ (k + 1) * endWordSeminorm D (k + 1) v := by ring

end EndWordSeminorm

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

/-- **Comparison of the word seminorms along two families.** If `Y j = ∑ i, c j i • X i` for
every `j`, then `P^Y_k ≤ (1 + ∑ j, ∑ i, |c j i|)^k P^X_k`. -/
theorem wordSeminorm_le_of_eq_sum (X : ι → LeftInvariantDerivation I G)
    {Y : κ → LeftInvariantDerivation I G} (c : κ → ι → ℝ) (hY : ∀ j, Y j = ∑ i, c j i • X i)
    (k : ℕ) (v : lieSmoothVectors I π) :
    wordSeminorm I π Y k v ≤
      (1 + ∑ j, ∑ i, |c j i|) ^ k * wordSeminorm I π X k v := by
  have h := endWordSeminorm_le_of_eq_sum (fun i ↦ lieSmoothVectorsDerivative I π (X i))
    (D' := fun j ↦ lieSmoothVectorsDerivative I π (Y j)) (fun j i ↦ algebraMap ℝ 𝕜 (c j i))
    (fun j ↦ by simp [hY j, lieSmoothVectorsDerivative_sum, lieSmoothVectorsDerivative_smul,
      algebraMap_smul]) k v
  simpa only [wordSeminorm_eq_endWordSeminorm, norm_algebraMap', Real.norm_eq_abs] using h

/-- **Comparison of the word seminorms with those along a basis.** For a real basis `b` of the
left-invariant derivations and any finite family `Y`,
`P^Y_k ≤ (1 + ∑ j, ∑ i, |b.repr (Y j) i|)^k P^b_k`. -/
theorem wordSeminorm_le_basis (b : Module.Basis ι ℝ (LeftInvariantDerivation I G))
    (Y : κ → LeftInvariantDerivation I G) (k : ℕ) (v : lieSmoothVectors I π) :
    wordSeminorm I π Y k v ≤
      (1 + ∑ j, ∑ i, |b.repr (Y j) i|) ^ k * wordSeminorm I π b k v :=
  wordSeminorm_le_of_eq_sum b (fun j i ↦ b.repr (Y j) i) (fun j ↦ (b.sum_repr (Y j)).symm) k v

/-- **The word seminorms along a finite family are bounded by those along a basis.** For a real
basis `b` of the left-invariant derivations and any finite family `Y`, the family `k ↦ P^Y_k` is
bounded by the family `k ↦ P^b_k`. For two bases, applying this in both directions shows that
the two families bound each other, so (with `WithSeminorms.congr`) they induce the same
topology. -/
theorem isBounded_wordSeminorm_basis (b : Module.Basis ι ℝ (LeftInvariantDerivation I G))
    (Y : κ → LeftInvariantDerivation I G) :
    Seminorm.IsBounded (wordSeminorm I π b) (wordSeminorm I π Y) LinearMap.id :=
  Seminorm.IsBounded.of_real fun k ↦ ⟨{k}, _, fun v ↦ by
    rw [Finset.sup_singleton]; exact wordSeminorm_le_basis b Y k v⟩

end ContRepresentation
