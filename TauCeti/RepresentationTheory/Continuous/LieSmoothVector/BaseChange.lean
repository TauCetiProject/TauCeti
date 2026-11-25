/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.BasisChange
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Enveloping

/-!
# Word seminorms along a basis of the complexified Lie algebra

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V` over a normed
field `𝕜` containing `ℝ` (for instance `𝕜 = ℂ`), and let `𝔤 = 𝕜 ⊗[ℝ] Lie(G)` be the base change of
the real Lie algebra of left-invariant derivations. The derived action extends `𝕜`-linearly to
`𝔤` (`ContRepresentation.lieSmoothVectorsBaseChangeDerivedAction`), with `dπ(a ⊗ X) = a dπ(X)`.

For a finite family `Z` in `𝔤` this file defines the word seminorms
`P^Z_k(v) = ∑_{|w| ≤ k} ‖dπ(Z_w) v‖` (`ContRepresentation.baseChangeWordSeminorm`). For
`Z = 1 ⊗ X` they are the real word seminorms of `X`
(`ContRepresentation.baseChangeWordSeminorm_one_tmul`). As in the real case, if
`Y j = ∑ i, c j i • Z i` with `c j i ∈ 𝕜`, then `P^Y_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^Z_k`
(`ContRepresentation.baseChangeWordSeminorm_le_of_eq_sum`). Every finite family in `𝔤` is a
`𝕜`-combination of a `𝕜`-basis, and of the base change `1 ⊗ b` of a real basis `b` of `Lie(G)`;
conversely each `1 ⊗ X` is a combination of a `𝕜`-basis. So the word seminorms along a
`𝕜`-basis of `𝔤` and along a real basis of `Lie(G)` bound each other: they define the same
topology on the smooth vectors.

## Main definitions

* `ContRepresentation.baseChangeWordAction`: the operator `dπ(Z_w)` of a word in a family of
  `𝕜 ⊗[ℝ] Lie(G)`.
* `ContRepresentation.baseChangeWordSeminorm`: the word seminorm `P^Z_k`.

## Main results

* `ContRepresentation.baseChangeWordSeminorm_one_tmul`: the word seminorms of `1 ⊗ X` are the
  real word seminorms of `X`.
* `ContRepresentation.baseChangeWordSeminorm_le_of_eq_sum`: the comparison along a
  `𝕜`-combination.
* `ContRepresentation.isBounded_baseChangeWordSeminorm_wordSeminorm_basis` and
  `ContRepresentation.isBounded_wordSeminorm_baseChangeWordSeminorm_basis`: the word seminorms
  along a real basis of `Lie(G)` and along a `𝕜`-basis of `𝕜 ⊗[ℝ] Lie(G)` bound each other.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.4.2–2.4.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold TensorProduct

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {ι κ μ : Type*}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The operators of words -/

variable (I π) in
/-- The operator `dπ(Z_w) = dπ(Z_{j₁}) ∘ ⋯ ∘ dπ(Z_{jₙ})` on smooth vectors attached to a word
`w = [j₁, …, jₙ]` in a family `Z` of `𝕜 ⊗[ℝ] Lie(G)`. -/
def baseChangeWordAction (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (w : List κ) :
    Module.End 𝕜 (lieSmoothVectors I π) :=
  (w.map fun j ↦ lieSmoothVectorsBaseChangeDerivedAction I π (Z j)).prod

@[simp]
theorem baseChangeWordAction_nil (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) :
    baseChangeWordAction I π Z [] = 1 :=
  (rfl)

@[simp]
theorem baseChangeWordAction_cons (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (j : κ)
    (w : List κ) :
    baseChangeWordAction I π Z (j :: w) =
      lieSmoothVectorsBaseChangeDerivedAction I π (Z j) * baseChangeWordAction I π Z w :=
  (rfl)

@[simp]
theorem baseChangeWordAction_append (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G)
    (w₁ w₂ : List κ) :
    baseChangeWordAction I π Z (w₁ ++ w₂) =
      baseChangeWordAction I π Z w₁ * baseChangeWordAction I π Z w₂ := by
  simp [baseChangeWordAction]

/-- The words in `1 ⊗ X` act as the words in `X`. -/
@[simp]
theorem baseChangeWordAction_one_tmul (X : ι → LeftInvariantDerivation I G) (w : List ι) :
    baseChangeWordAction I π (fun i ↦ (1 : 𝕜) ⊗ₜ X i) w = wordAction I π X w := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih]

/-! ### The word seminorms -/

variable [Fintype κ]

variable (I π) in
/-- The word seminorm `P^Z_k(v) = ∑_{|w| ≤ k} ‖dπ(Z_w) v‖` on smooth vectors, along a family `Z`
of `𝕜 ⊗[ℝ] Lie(G)`. -/
def baseChangeWordSeminorm (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) :
    Seminorm 𝕜 (lieSmoothVectors I π) :=
  ∑ w : BoundedWord κ k,
    (normSeminorm 𝕜 V).comp
      ((lieSmoothVectors I π).subtype ∘ₗ baseChangeWordAction I π Z (List.ofFn w.2))

theorem baseChangeWordSeminorm_apply (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) :
    baseChangeWordSeminorm I π Z k v =
      ∑ w : BoundedWord κ k, ‖(baseChangeWordAction I π Z (List.ofFn w.2) v : V)‖ := by
  rw [← FunLike.coeAddMonoidHom_apply]
  simp [baseChangeWordSeminorm, map_sum, Finset.sum_apply]

/-- **The word seminorms of `1 ⊗ X` are the real word seminorms of `X`.** -/
@[simp]
theorem baseChangeWordSeminorm_one_tmul (X : κ → LeftInvariantDerivation I G) (k : ℕ) :
    baseChangeWordSeminorm I π (fun i ↦ (1 : 𝕜) ⊗ₜ X i) k = wordSeminorm I π X k := by
  ext v
  rw [baseChangeWordSeminorm_apply, wordSeminorm_apply]
  simp

/-- The word seminorm of order zero is the norm of `V`. -/
@[simp]
theorem baseChangeWordSeminorm_zero (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G)
    (v : lieSmoothVectors I π) : baseChangeWordSeminorm I π Z 0 v = ‖(v : V)‖ := by
  rw [baseChangeWordSeminorm_apply, Fintype.sum_sigma, Fin.sum_univ_one]
  simp

/-- **The recursion for the word seminorms.** `P^Z_{k+1}(v) = ‖v‖ + ∑ j, P^Z_k(dπ(Z_j) v)`. -/
theorem baseChangeWordSeminorm_succ (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) :
    baseChangeWordSeminorm I π Z (k + 1) v = ‖(v : V)‖ + ∑ j,
      baseChangeWordSeminorm I π Z k (lieSmoothVectorsBaseChangeDerivedAction I π (Z j) v) := by
  rw [baseChangeWordSeminorm_apply, BoundedWord.sum_succ (M := ℝ)]
  simp only [BoundedWord.ofFn_nil, baseChangeWordAction_nil, BoundedWord.ofFn_snoc,
    baseChangeWordAction_append, baseChangeWordAction_cons, mul_one, one_apply_eq_self,
    mul_apply_eq_comp, baseChangeWordSeminorm_apply]

/-- The word seminorms increase with the order: `P^Z_k ≤ P^Z_{k+1}`. -/
theorem baseChangeWordSeminorm_le_succ (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) :
    baseChangeWordSeminorm I π Z k v ≤ baseChangeWordSeminorm I π Z (k + 1) v := by
  classical
  rw [baseChangeWordSeminorm_apply, baseChangeWordSeminorm_apply]
  exact Finset.sum_le_sum_of_injOn BoundedWord.castSucc BoundedWord.castSucc_injective.injOn
    (Finset.subset_univ _) (fun _ _ ↦ by rw [BoundedWord.ofFn_castSucc]) fun _ _ _ ↦
      norm_nonneg _

/-- The word seminorms increase with the order: `P^Z_k ≤ P^Z_l` for `k ≤ l`. -/
theorem baseChangeWordSeminorm_mono (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) {k l : ℕ}
    (hkl : k ≤ l) (v : lieSmoothVectors I π) :
    baseChangeWordSeminorm I π Z k v ≤ baseChangeWordSeminorm I π Z l v :=
  monotone_nat_of_le_succ (fun n ↦ baseChangeWordSeminorm_le_succ Z n v) hkl

/-- **The derivative estimate along a family element.** `P^Z_k(dπ(Z_j) v) ≤ P^Z_{k+1}(v)`. -/
theorem baseChangeWordSeminorm_derivedAction_le (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G)
    (k : ℕ) (j : κ) (v : lieSmoothVectors I π) :
    baseChangeWordSeminorm I π Z k (lieSmoothVectorsBaseChangeDerivedAction I π (Z j) v) ≤
      baseChangeWordSeminorm I π Z (k + 1) v := by
  rw [baseChangeWordSeminorm_succ]
  exact le_add_of_nonneg_of_le (norm_nonneg _) (Finset.single_le_sum
    (f := fun j ↦ baseChangeWordSeminorm I π Z k
      (lieSmoothVectorsBaseChangeDerivedAction I π (Z j) v))
    (fun _ _ ↦ apply_nonneg _ _) (Finset.mem_univ j))

/-- **The derivative estimate.** If `Y = ∑ j, c j • Z j`, then
`P^Z_k(dπ(Y) v) ≤ (∑ j, ‖c j‖) P^Z_{k+1}(v)`. -/
theorem baseChangeWordSeminorm_derivedAction_le_of_eq_sum
    (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ)
    {Y : 𝕜 ⊗[ℝ] LeftInvariantDerivation I G} (c : κ → 𝕜) (hY : Y = ∑ j, c j • Z j)
    (v : lieSmoothVectors I π) :
    baseChangeWordSeminorm I π Z k (lieSmoothVectorsBaseChangeDerivedAction I π Y v) ≤
      (∑ j, ‖c j‖) * baseChangeWordSeminorm I π Z (k + 1) v := by
  have hd : lieSmoothVectorsBaseChangeDerivedAction I π Y v =
      ∑ j, c j • lieSmoothVectorsBaseChangeDerivedAction I π (Z j) v := by
    simp [hY]
  rw [hd, Finset.sum_mul]
  refine (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans
    (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [map_smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (baseChangeWordSeminorm_derivedAction_le Z k j v)
    (norm_nonneg _)

variable [Fintype μ]

/-- **Comparison of the word seminorms along two families.** If `Y j = ∑ i, c j i • Z i` with
`c j i ∈ 𝕜`, then `P^Y_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^Z_k`. -/
theorem baseChangeWordSeminorm_le_of_eq_sum (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G)
    {Y : μ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G} (c : μ → κ → 𝕜)
    (hY : ∀ j, Y j = ∑ i, c j i • Z i) (k : ℕ) (v : lieSmoothVectors I π) :
    baseChangeWordSeminorm I π Y k v ≤
      (1 + ∑ j, ∑ i, ‖c j i‖) ^ k * baseChangeWordSeminorm I π Z k v := by
  set S := ∑ j, ∑ i, ‖c j i‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    have hC : 1 ≤ (1 + S) ^ k := one_le_pow₀ (le_add_of_nonneg_right hS)
    have hv : ‖(v : V)‖ ≤ (1 + S) ^ k * baseChangeWordSeminorm I π Z (k + 1) v := by
      rw [← baseChangeWordSeminorm_zero Z]
      exact (baseChangeWordSeminorm_mono Z (Nat.zero_le _) v).trans
        (le_mul_of_one_le_left (apply_nonneg _ _) hC)
    have hsum : ∑ j, baseChangeWordSeminorm I π Y k
        (lieSmoothVectorsBaseChangeDerivedAction I π (Y j) v) ≤
        (1 + S) ^ k * (S * baseChangeWordSeminorm I π Z (k + 1) v) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ ↦ (ih _).trans ?_
      exact mul_le_mul_of_nonneg_left
        (baseChangeWordSeminorm_derivedAction_le_of_eq_sum Z k (c j) (hY j) v)
        (pow_nonneg (by positivity) _)
    rw [baseChangeWordSeminorm_succ]
    calc ‖(v : V)‖ + ∑ j, baseChangeWordSeminorm I π Y k
          (lieSmoothVectorsBaseChangeDerivedAction I π (Y j) v)
      _ ≤ (1 + S) ^ k * baseChangeWordSeminorm I π Z (k + 1) v +
          (1 + S) ^ k * (S * baseChangeWordSeminorm I π Z (k + 1) v) := add_le_add hv hsum
      _ = (1 + S) ^ (k + 1) * baseChangeWordSeminorm I π Z (k + 1) v := by ring

/-! ### Real and `𝕜`-bases -/

/-- **The word seminorms along a finite family of `𝕜 ⊗[ℝ] Lie(G)` are bounded by those along a
real basis of `Lie(G)`**: every element of `𝕜 ⊗[ℝ] Lie(G)` is a `𝕜`-combination of the base
change `1 ⊗ b` of a real basis `b`. -/
theorem isBounded_wordSeminorm_baseChangeWordSeminorm_basis [Fintype ι]
    (b : Module.Basis ι ℝ (LeftInvariantDerivation I G))
    (Z : μ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) :
    Seminorm.IsBounded (wordSeminorm I π b) (baseChangeWordSeminorm I π Z) LinearMap.id := by
  let b' := Algebra.TensorProduct.basis 𝕜 b
  refine Seminorm.IsBounded.of_real fun k ↦
    ⟨{k}, (1 + ∑ j, ∑ i, ‖b'.repr (Z j) i‖) ^ k, fun v ↦ ?_⟩
  rw [Finset.sup_singleton, LinearMap.id_apply, ← baseChangeWordSeminorm_one_tmul (𝕜 := 𝕜)]
  refine baseChangeWordSeminorm_le_of_eq_sum _ (fun j i ↦ b'.repr (Z j) i) (fun j ↦ ?_) k v
  conv_lhs => rw [← b'.sum_repr (Z j)]
  simp [b', Algebra.TensorProduct.basis_apply]

/-- **The word seminorms along a finite real family are bounded by those along a `𝕜`-basis of
`𝕜 ⊗[ℝ] Lie(G)`**: each `1 ⊗ X i` is a `𝕜`-combination of the basis. With
`ContRepresentation.isBounded_wordSeminorm_baseChangeWordSeminorm_basis`, the word seminorms
along a real basis of `Lie(G)` and along a `𝕜`-basis of `𝕜 ⊗[ℝ] Lie(G)` bound each other. -/
theorem isBounded_baseChangeWordSeminorm_wordSeminorm_basis
    (b : Module.Basis μ 𝕜 (𝕜 ⊗[ℝ] LeftInvariantDerivation I G)) [Fintype ι]
    (X : ι → LeftInvariantDerivation I G) :
    Seminorm.IsBounded (baseChangeWordSeminorm I π b) (wordSeminorm I π X) LinearMap.id := by
  refine Seminorm.IsBounded.of_real fun k ↦
    ⟨{k}, (1 + ∑ j, ∑ i, ‖b.repr (1 ⊗ₜ X j) i‖) ^ k, fun v ↦ ?_⟩
  rw [Finset.sup_singleton, LinearMap.id_apply, ← baseChangeWordSeminorm_one_tmul (𝕜 := 𝕜)]
  exact baseChangeWordSeminorm_le_of_eq_sum b (fun j i ↦ b.repr (1 ⊗ₜ X j) i)
    (fun j ↦ (b.sum_repr _).symm) k v

end ContRepresentation
