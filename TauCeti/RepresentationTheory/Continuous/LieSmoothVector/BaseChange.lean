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
`P^Z_k(v) = ∑_{|w| ≤ k} ‖dπ(Z_w) v‖` (`ContRepresentation.baseChangeWordSeminorm`), as the word
seminorms `Seminorm.endWordSeminorm` of the norm along the operators `dπ(Z_j)`. For `Z = 1 ⊗ X`
they are the real word seminorms of `X` (`ContRepresentation.baseChangeWordSeminorm_one_tmul`). The
comparison `Seminorm.endWordSeminorm_le_of_eq_sum` for families of operators, which also
gives the real comparison `ContRepresentation.wordSeminorm_le_of_eq_sum`, shows: if
`Y j = ∑ i, c j i • Z i` with `c j i ∈ 𝕜`, then `P^Y_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^Z_k`
(`ContRepresentation.baseChangeWordSeminorm_le_of_eq_sum`). Every finite family in `𝔤` is a
`𝕜`-combination of a `𝕜`-basis, and of the base change `1 ⊗ b` of a real basis `b` of `Lie(G)`;
conversely each `1 ⊗ X` is a combination of a `𝕜`-basis. So the word seminorms along a
`𝕜`-basis of `𝔤` and along a real basis of `Lie(G)` bound each other: they define the same
topology on the smooth vectors.

## Main definitions

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {ι κ μ : Type*}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-! ### The word seminorms -/

variable [Fintype κ]

variable (I π) in
/-- The word seminorm `P^Z_k(v) = ∑_{|w| ≤ k} ‖dπ(Z_w) v‖` on smooth vectors, along a family `Z`
of `𝕜 ⊗[ℝ] Lie(G)`: the word seminorm of the norm of `V` along the operators `dπ(Z_j)`. -/
def baseChangeWordSeminorm (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) :
    Seminorm 𝕜 (lieSmoothVectors I π) :=
  ((normSeminorm 𝕜 V).comp (lieSmoothVectors I π).subtype).endWordSeminorm
    (fun j ↦ lieSmoothVectorsBaseChangeDerivedAction I π (Z j)) k

/-- The word seminorm along `Z` is the word seminorm of the norm of `V` along the operators
`dπ(Z_j)`. -/
theorem baseChangeWordSeminorm_eq_endWordSeminorm
    (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) :
    baseChangeWordSeminorm I π Z k =
      ((normSeminorm 𝕜 V).comp (lieSmoothVectors I π).subtype).endWordSeminorm
        (fun j ↦ lieSmoothVectorsBaseChangeDerivedAction I π (Z j)) k :=
  (rfl)

/-- **The word seminorms of `1 ⊗ X` are the real word seminorms of `X`.** -/
@[simp]
theorem baseChangeWordSeminorm_one_tmul (X : κ → LeftInvariantDerivation I G) (k : ℕ) :
    baseChangeWordSeminorm I π (fun i ↦ (1 : 𝕜) ⊗ₜ X i) k = wordSeminorm I π X k := by
  simp [baseChangeWordSeminorm_eq_endWordSeminorm, wordSeminorm_eq_endWordSeminorm]

variable [Fintype μ]

/-- **Comparison of the word seminorms along two families.** If `Y j = ∑ i, c j i • Z i` with
`c j i ∈ 𝕜`, then `P^Y_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^Z_k`. -/
theorem baseChangeWordSeminorm_le_of_eq_sum (Z : κ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G)
    {Y : μ → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G} (c : μ → κ → 𝕜)
    (hY : ∀ j, Y j = ∑ i, c j i • Z i) (k : ℕ) (v : lieSmoothVectors I π) :
    baseChangeWordSeminorm I π Y k v ≤
      (1 + ∑ j, ∑ i, ‖c j i‖) ^ k * baseChangeWordSeminorm I π Z k v := by
  simp only [baseChangeWordSeminorm_eq_endWordSeminorm]
  exact Seminorm.endWordSeminorm_le_of_eq_sum _ _ c (fun j ↦ by simp [hY j]) k v

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
