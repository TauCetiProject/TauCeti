/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector

/-!
# Word and Sobolev seminorms on the smooth vectors of a Lie group representation

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V` over a
normed field `𝕜`, and let `dπ(X) = lieSmoothVectorsDerivative I π X` be the derived action of a
left-invariant derivation `X` on the smooth vectors `lieSmoothVectors I π`.

Fix a family `X : ι → LeftInvariantDerivation I G` of Lie algebra elements, for instance a basis.
For a word `w = i₁ ⋯ iₙ` in `ι` write `dπ(X_w) = dπ(X_{i₁}) ∘ ⋯ ∘ dπ(X_{iₙ})`. The *word
seminorm* of order `k` is

`P_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖`,

summed over all words of length at most `k`. For `ι = Fin m` the *Sobolev seminorm* of order `k`
(Bernstein–Krötz) uses only the ordered monomials `X^α = X₁^{α₁} ⋯ X_m^{α_m}`:

`Q_k(v) = (∑_{|α| ≤ k} ‖dπ(X^α) v‖²)^{1/2}`.

Every ordered monomial is a word, so `Q_k ≤ P_k`
(`ContRepresentation.sobolevSeminorm_le_wordSeminorm`).

## Main definitions

* `TauCeti.BoundedWord ι k`: the words in `ι` of length at most `k`.
* `TauCeti.monomialWord α`: the word `1^{α₁} ⋯ m^{α_m}` of an exponent vector.
* `TauCeti.SobolevIndex m k`: the exponent vectors `α : Fin m → ℕ` with `|α| ≤ k`.
* `ContRepresentation.wordAction I π X w`: the operator `dπ(X_w)` of a word `w`.
* `ContRepresentation.wordSeminorm I π X k`: the word seminorm `P_k`.
* `ContRepresentation.sobolevSeminorm I π X k`: the Sobolev seminorm `Q_k`.

## Main results

* `ContRepresentation.wordSeminorm_apply`, `ContRepresentation.sobolevSeminorm_apply`: the two
  seminorms as explicit sums.
* `ContRepresentation.wordSeminorm_zero`: `P_0` is the norm.
* `ContRepresentation.sobolevSeminorm_le_wordSeminorm`: `Q_k ≤ P_k`.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.4.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

/-! ### Words and ordered monomials -/

/-- The words in `ι` of length at most `k`: a word of length `n ≤ k` is `⟨n, w⟩` with
`w : Fin n → ι`. -/
abbrev BoundedWord (ι : Type*) (k : ℕ) : Type _ :=
  Σ n : Fin (k + 1), Fin n → ι

variable {m : ℕ}

/-- The ordered monomial word `1^{α₁} 2^{α₂} ⋯ m^{α_m}` of an exponent vector `α`. -/
def monomialWord (α : Fin m → ℕ) : List (Fin m) :=
  (List.finRange m).flatMap fun i ↦ List.replicate (α i) i

/-- The ordered monomial word of `α` has length `|α|`. -/
theorem length_monomialWord (α : Fin m → ℕ) : (monomialWord α).length = ∑ i, α i := by
  simp [monomialWord, List.length_flatMap, Fin.sum_univ_def]

/-- The letter `i` occurs `α i` times in the ordered monomial word of `α`. -/
theorem count_monomialWord (α : Fin m → ℕ) (i : Fin m) : (monomialWord α).count i = α i := by
  rw [monomialWord, List.count_flatMap, ← Fin.sum_univ_def]
  simp [List.count_replicate]

/-- An ordered monomial word determines its exponent vector. -/
theorem monomialWord_injective : Function.Injective (monomialWord (m := m)) := fun α β h ↦
  funext fun i ↦ by rw [← count_monomialWord α i, ← count_monomialWord β i, h]

/-- The exponent vectors `α : Fin m → ℕ` of total degree `|α| = ∑ i, α i ≤ k`, with entries
recorded in `Fin (k + 1)` so that they form a finite type. -/
abbrev SobolevIndex (m k : ℕ) : Type :=
  {α : Fin m → Fin (k + 1) // ∑ i, (α i : ℕ) ≤ k}

/-- The exponent vector in `ℕ` of an index in `SobolevIndex m k`. -/
def SobolevIndex.exponent {k : ℕ} (α : SobolevIndex m k) (i : Fin m) : ℕ :=
  α.val i

/-- The `i`-th entry of the exponent vector of `α`. -/
@[simp]
theorem SobolevIndex.exponent_apply {k : ℕ} (α : SobolevIndex m k) (i : Fin m) :
    α.exponent i = α.val i :=
  (rfl)

/-- An index in `SobolevIndex m k` is determined by its exponent vector. -/
theorem SobolevIndex.exponent_injective {k : ℕ} :
    Function.Injective (SobolevIndex.exponent (m := m) (k := k)) := fun _ _ h ↦
  Subtype.ext (funext fun i ↦ Fin.ext (congrFun h i))

/-- The ordered monomial word of an index in `SobolevIndex m k`, as a word of length at most
`k`. -/
def SobolevIndex.toBoundedWord {k : ℕ} (α : SobolevIndex m k) : BoundedWord (Fin m) k :=
  ⟨⟨(monomialWord α.exponent).length, by
      rw [length_monomialWord]; exact Nat.lt_succ_of_le α.property⟩,
    (monomialWord α.exponent).get⟩

/-- The word `SobolevIndex.toBoundedWord α` spells the ordered monomial word of `α`. -/
@[simp]
theorem SobolevIndex.ofFn_toBoundedWord {k : ℕ} (α : SobolevIndex m k) :
    List.ofFn α.toBoundedWord.2 = monomialWord α.exponent :=
  List.ofFn_get _

/-- Distinct ordered monomials give distinct words. -/
theorem SobolevIndex.toBoundedWord_injective {k : ℕ} :
    Function.Injective (SobolevIndex.toBoundedWord (m := m) (k := k)) := fun α β h ↦ by
  have := congrArg (fun w : BoundedWord (Fin m) k ↦ List.ofFn w.2) h
  simp only [SobolevIndex.ofFn_toBoundedWord] at this
  exact SobolevIndex.exponent_injective (monomialWord_injective this)

end TauCeti

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  (π : ContRepresentation 𝕜 G V)

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {I π}

/-! ### The word seminorms -/

variable {ι : Type*}

variable (I π) in
/-- The operator `dπ(X_w) = dπ(X_{i₁}) ∘ ⋯ ∘ dπ(X_{iₙ})` on smooth vectors attached to a word
`w = [i₁, …, iₙ]`. -/
def wordAction (X : ι → LeftInvariantDerivation I G) (w : List ι) :
    Module.End 𝕜 (lieSmoothVectors I π) :=
  (w.map fun i ↦ lieSmoothVectorsDerivative I π (X i)).prod

/-- The empty word acts as the identity. -/
@[simp]
theorem wordAction_nil (X : ι → LeftInvariantDerivation I G) : wordAction I π X [] = 1 :=
  (rfl)

/-- `dπ(X_{i w}) = dπ(X_i) ∘ dπ(X_w)`. -/
@[simp]
theorem wordAction_cons (X : ι → LeftInvariantDerivation I G) (i : ι) (w : List ι) :
    wordAction I π X (i :: w) = lieSmoothVectorsDerivative I π (X i) * wordAction I π X w :=
  (rfl)

/-- A one-letter word `[i]` acts as `dπ(X_i)`. Not `@[simp]`: `wordAction_cons` and
`wordAction_nil` already rewrite it. -/
theorem wordAction_singleton (X : ι → LeftInvariantDerivation I G) (i : ι) :
    wordAction I π X [i] = lieSmoothVectorsDerivative I π (X i) := by
  simp

/-- `dπ(X_{w₁ w₂}) = dπ(X_{w₁}) ∘ dπ(X_{w₂})`. -/
@[simp]
theorem wordAction_append (X : ι → LeftInvariantDerivation I G) (w₁ w₂ : List ι) :
    wordAction I π X (w₁ ++ w₂) = wordAction I π X w₁ * wordAction I π X w₂ := by
  simp [wordAction]

variable [Fintype ι]

variable (I π) in
/-- The word seminorm `P_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖` on smooth vectors, summed over all
words `w` in `ι` of length at most `k`. -/
def wordSeminorm (X : ι → LeftInvariantDerivation I G) (k : ℕ) :
    Seminorm 𝕜 (lieSmoothVectors I π) :=
  ∑ w : BoundedWord ι k,
    (normSeminorm 𝕜 V).comp
      ((lieSmoothVectors I π).subtype ∘ₗ wordAction I π X (List.ofFn w.2))

/-- The word seminorm as an explicit sum over words. -/
theorem wordSeminorm_apply (X : ι → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) :
    wordSeminorm I π X k v =
      ∑ w : BoundedWord ι k, ‖(wordAction I π X (List.ofFn w.2) v : V)‖ := by
  rw [← FunLike.coeAddMonoidHom_apply]
  simp [wordSeminorm, map_sum, Finset.sum_apply]

/-- The word seminorm of order zero is the norm of `V`. -/
@[simp]
theorem wordSeminorm_zero (X : ι → LeftInvariantDerivation I G) (v : lieSmoothVectors I π) :
    wordSeminorm I π X 0 v = ‖(v : V)‖ := by
  rw [wordSeminorm_apply, Fintype.sum_sigma, Fin.sum_univ_one]
  simp

/-! ### The Sobolev seminorms -/

variable {m : ℕ}

variable (I π) in
/-- The vector `(dπ(X^α) v)_{|α| ≤ k}` of ordered monomial derivatives, in the `ℓ²` product. -/
def sobolevVector (X : Fin m → LeftInvariantDerivation I G) (k : ℕ) :
    lieSmoothVectors I π →ₗ[𝕜] PiLp 2 (fun _ : SobolevIndex m k ↦ V) :=
  (WithLp.linearEquiv 2 𝕜 _).symm.toLinearMap ∘ₗ
    LinearMap.pi fun α ↦
      (lieSmoothVectors I π).subtype ∘ₗ wordAction I π X (monomialWord α.exponent)

/-- The `α`-component of `sobolevVector` is `dπ(X^α) v`. -/
@[simp]
theorem sobolevVector_apply (X : Fin m → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) (α : SobolevIndex m k) :
    sobolevVector I π X k v α = (wordAction I π X (monomialWord α.exponent) v : V) :=
  (rfl)

variable (I π) in
/-- The Sobolev seminorm `Q_k(v) = (∑_{|α| ≤ k} ‖dπ(X^α) v‖²)^{1/2}` of Bernstein–Krötz, over
the ordered monomials `X^α = X₁^{α₁} ⋯ X_m^{α_m}` of degree at most `k`. -/
def sobolevSeminorm (X : Fin m → LeftInvariantDerivation I G) (k : ℕ) :
    Seminorm 𝕜 (lieSmoothVectors I π) :=
  (normSeminorm 𝕜 (PiLp 2 fun _ : SobolevIndex m k ↦ V)).comp (sobolevVector I π X k)

/-- The Sobolev seminorm as an explicit square root of a sum of squares. -/
theorem sobolevSeminorm_apply (X : Fin m → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) :
    sobolevSeminorm I π X k v =
      √(∑ α : SobolevIndex m k, ‖(wordAction I π X (monomialWord α.exponent) v : V)‖ ^ 2) := by
  simp [sobolevSeminorm, PiLp.norm_eq_of_L2]

/-- The Sobolev seminorm is bounded by the word seminorm: every ordered monomial is a word, and
the `ℓ²` norm of a finite family is at most its `ℓ¹` norm. -/
theorem sobolevSeminorm_le_wordSeminorm (X : Fin m → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) : sobolevSeminorm I π X k v ≤ wordSeminorm I π X k v := by
  classical
  set b : BoundedWord (Fin m) k → ℝ := fun w ↦ ‖(wordAction I π X (List.ofFn w.2) v : V)‖
  have hb : ∀ α : SobolevIndex m k,
      ‖(wordAction I π X (monomialWord α.exponent) v : V)‖ = b α.toBoundedWord := fun α ↦ by
    simp only [b, SobolevIndex.ofFn_toBoundedWord]
  have hsum : ∑ α : SobolevIndex m k, b α.toBoundedWord ≤ ∑ w, b w := by
    rw [← Finset.sum_image fun _ _ _ _ h ↦ SobolevIndex.toBoundedWord_injective h]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ norm_nonneg _
  rw [sobolevSeminorm_apply, wordSeminorm_apply, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, ?_⟩
  simp_rw [hb]
  calc ∑ α : SobolevIndex m k, b α.toBoundedWord ^ 2
    _ ≤ (∑ α : SobolevIndex m k, b α.toBoundedWord) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ (∑ w, b w) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hsum 2

end ContRepresentation
