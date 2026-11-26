/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.Analysis.Normed.Module.Seminorm.Word
public import TauCeti.Data.List.MonomialWord
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
(`ContRepresentation.sobolevSeminorm_le_wordSeminorm`). The word seminorms increase with `k`, and
the derived action lowers the order by one: if `Y = ∑ i, c i • X i`, then
`P_k(dπ(Y) v) ≤ (∑ i, |c i|) P_{k+1}(v)`, because appending a letter to the words of length at most
`k` gives distinct words of length at most `k + 1`.

The word seminorms and these properties are the case of the norm on the smooth vectors and
`D i = dπ(X_i)` of the word seminorms `P^D_k(x) = ∑_{|w| ≤ k} p(D_w x)` of a seminorm `p` along a
family `D` of operators on a module (`Seminorm.endWordSeminorm`, in
`TauCeti.Analysis.Normed.Module.Seminorm.Word`).

## Main definitions

* `TauCeti.SobolevIndex m k`: the exponent vectors `α : Fin m → ℕ` with `|α| ≤ k`.
* `ContRepresentation.wordAction I π X w`: the operator `dπ(X_w)` of a word `w`, for a
  representation over any ring.
* `ContRepresentation.wordSeminorm I π X k`: the word seminorm `P_k`.
* `ContRepresentation.sobolevSeminorm I π X k`: the Sobolev seminorm `Q_k`.

## Main results

* `ContRepresentation.wordSeminorm_apply`, `ContRepresentation.sobolevSeminorm_apply`: the two
  seminorms as explicit sums.
* `ContRepresentation.wordSeminorm_zero`: `P_0` is the norm.
* `ContRepresentation.wordSeminorm_succ`: `P_{k+1}(v) = ‖v‖ + ∑ i, P_k(dπ(X_i) v)`.
* `ContRepresentation.sobolevSeminorm_le_wordSeminorm`: `Q_k ≤ P_k`.
* `ContRepresentation.wordSeminorm_mono`: `P_k ≤ P_l` for `k ≤ l`.
* `ContRepresentation.wordSeminorm_lieSmoothVectorsDerivative_le`: `P_k(dπ(X_i) v) ≤ P_{k+1}(v)`.
* `ContRepresentation.wordSeminorm_lieSmoothVectorsDerivative_le_basis`: for a real basis `b`,
  `P_k(dπ(Y) v) ≤ (∑ i, |b.repr Y i|) P_{k+1}(v)`.
* `TauCeti.exists_sobolevIndex_monomialWord_eq`: a sorted word of length at most `k` is the
  ordered monomial word `TauCeti.monomialWord α` of an index `α` in `SobolevIndex m k`.
* `ContRepresentation.wordSeminorm_trivial`, `ContRepresentation.sobolevSeminorm_trivial`: for
  the trivial representation, every nonempty word acts by zero, so `P_k = Q_k = ‖·‖`.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.4.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

/-! ### Ordered monomials -/

variable {m : ℕ}

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

/-- A sorted word of length at most `k` is the ordered monomial word of an index in
`SobolevIndex m k`. -/
theorem exists_sobolevIndex_monomialWord_eq {k : ℕ} {w : List (Fin m)}
    (hw : w.Pairwise (· ≤ ·)) (hk : w.length ≤ k) :
    ∃ α : SobolevIndex m k, monomialWord α.exponent = w := by
  have hsum : ∑ i, w.count i = w.length := by
    rw [← length_monomialWord, monomialWord_count hw]
  refine ⟨⟨fun i ↦ ⟨w.count i, Nat.lt_succ_of_le (List.count_le_length.trans hk)⟩, ?_⟩, ?_⟩
  · simpa [hsum] using hk
  · refine (congrArg monomialWord (funext fun i ↦ ?_)).trans (monomialWord_count hw)
    simp only [SobolevIndex.exponent_apply]

end TauCeti

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {I}

/-! ### The operators of words -/

section WordAction

variable {R : Type*} [Ring R] [Module R V] [SMulCommClass ℝ R V] [ContinuousConstSMul R V]
  (π : ContRepresentation R G V)

variable {π}

variable {ι : Type*}

variable (I π) in
/-- The operator `dπ(X_w) = dπ(X_{i₁}) ∘ ⋯ ∘ dπ(X_{iₙ})` on smooth vectors attached to a word
`w = [i₁, …, iₙ]`. -/
def wordAction (X : ι → LeftInvariantDerivation I G) (w : List ι) :
    Module.End R (lieSmoothVectors I π) :=
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

/-- For the trivial representation, every nonempty word acts by zero. -/
theorem wordAction_trivial_of_ne_nil (X : ι → LeftInvariantDerivation I G) {w : List ι}
    (hw : w ≠ []) : wordAction I (trivial R G V) X w = 0 := by
  obtain ⟨i, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp

end WordAction

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  (π : ContRepresentation 𝕜 G V)

variable {π}

/-! ### The word seminorms along a family of Lie algebra elements -/

variable {ι : Type*}

variable [Fintype ι]

variable (I π) in
/-- The word seminorm `P_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖` on smooth vectors, summed over all
words `w` in `ι` of length at most `k`. -/
def wordSeminorm (X : ι → LeftInvariantDerivation I G) (k : ℕ) :
    Seminorm 𝕜 (lieSmoothVectors I π) :=
  ((normSeminorm 𝕜 V).comp (lieSmoothVectors I π).subtype).endWordSeminorm
    (fun i ↦ lieSmoothVectorsDerivative I π (X i)) k

/-- The word seminorm along `X` is the word seminorm of the norm of `V` along the operators
`dπ(X_i)`. -/
theorem wordSeminorm_eq_endWordSeminorm (X : ι → LeftInvariantDerivation I G) (k : ℕ) :
    wordSeminorm I π X k =
      ((normSeminorm 𝕜 V).comp (lieSmoothVectors I π).subtype).endWordSeminorm
        (fun i ↦ lieSmoothVectorsDerivative I π (X i)) k :=
  (rfl)

/-- The word seminorm as an explicit sum over words. -/
theorem wordSeminorm_apply (X : ι → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) :
    wordSeminorm I π X k v =
      ∑ w : BoundedWord ι k, ‖(wordAction I π X (List.ofFn w.2) v : V)‖ := by
  simp [wordSeminorm_eq_endWordSeminorm, Seminorm.endWordSeminorm_apply, wordAction]

/-- The word seminorm of order zero is the norm of `V`. -/
@[simp]
theorem wordSeminorm_zero (X : ι → LeftInvariantDerivation I G) (v : lieSmoothVectors I π) :
    wordSeminorm I π X 0 v = ‖(v : V)‖ := by
  simp [wordSeminorm_eq_endWordSeminorm]

/-- **The recursion for the word seminorms.** `P_{k+1}(v) = ‖v‖ + ∑ i, P_k(dπ(X_i) v)`: a word
of length at most `k + 1` is empty or a word of length at most `k` followed by a letter `i`, and
`dπ(X_{w i}) v = dπ(X_w) dπ(X_i) v`. -/
theorem wordSeminorm_succ (X : ι → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) :
    wordSeminorm I π X (k + 1) v =
      ‖(v : V)‖ + ∑ i, wordSeminorm I π X k (lieSmoothVectorsDerivative I π (X i) v) := by
  simp only [wordSeminorm_eq_endWordSeminorm, Seminorm.endWordSeminorm_succ, Seminorm.comp_apply,
    coe_normSeminorm, Submodule.coe_subtype]

/-! ### Monotonicity and the derivative estimate -/

/-- The word seminorms increase with the order: `P_k ≤ P_{k+1}`. -/
theorem wordSeminorm_le_succ (X : ι → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) : wordSeminorm I π X k v ≤ wordSeminorm I π X (k + 1) v :=
  Seminorm.endWordSeminorm_le_succ _ _ k v

/-- The word seminorms increase with the order: `P_k ≤ P_l` for `k ≤ l`. -/
theorem wordSeminorm_mono (X : ι → LeftInvariantDerivation I G) {k l : ℕ} (hkl : k ≤ l)
    (v : lieSmoothVectors I π) : wordSeminorm I π X k v ≤ wordSeminorm I π X l v :=
  Seminorm.endWordSeminorm_mono _ _ hkl v

/-- **The derivative estimate along a family element.** `P_k(dπ(X_i) v) ≤ P_{k+1}(v)` for the
word seminorms along any family `X`. -/
theorem wordSeminorm_lieSmoothVectorsDerivative_le (X : ι → LeftInvariantDerivation I G)
    (k : ℕ) (i : ι) (v : lieSmoothVectors I π) :
    wordSeminorm I π X k (lieSmoothVectorsDerivative I π (X i) v) ≤
      wordSeminorm I π X (k + 1) v :=
  Seminorm.endWordSeminorm_apply_le _ _ k i v

section RealCombination

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

/-- **The derivative estimate.** If `Y = ∑ i, c i • X i`, then
`P_k(dπ(Y) v) ≤ (∑ i, |c i|) P_{k+1}(v)`. -/
theorem wordSeminorm_lieSmoothVectorsDerivative_le_of_eq_sum
    (X : ι → LeftInvariantDerivation I G) (k : ℕ) {Y : LeftInvariantDerivation I G}
    (c : ι → ℝ) (hY : Y = ∑ i, c i • X i) (v : lieSmoothVectors I π) :
    wordSeminorm I π X k (lieSmoothVectorsDerivative I π Y v) ≤
      (∑ i, |c i|) * wordSeminorm I π X (k + 1) v := by
  have h := Seminorm.endWordSeminorm_apply_le_of_eq_sum
    ((normSeminorm 𝕜 V).comp (lieSmoothVectors I π).subtype)
    (fun i ↦ lieSmoothVectorsDerivative I π (X i)) k (fun i ↦ algebraMap ℝ 𝕜 (c i))
    (A := lieSmoothVectorsDerivative I π Y) (by rw [hY, lieSmoothVectorsDerivative_sum_smul]) v
  simp only [← wordSeminorm_eq_endWordSeminorm, norm_algebraMap', Real.norm_eq_abs] at h
  exact h

/-- **The derivative estimate for a basis** (`P_k(dπ(Y) v) ≤ C_{Y} P_{k+1}(v)`). For a real basis
`b` of the left-invariant derivations, `P_k(dπ(Y) v) ≤ (∑ i, |b.repr Y i|) P_{k+1}(v)`, where the
seminorms are taken along `b`. -/
theorem wordSeminorm_lieSmoothVectorsDerivative_le_basis
    (b : Module.Basis ι ℝ (LeftInvariantDerivation I G)) (k : ℕ)
    (Y : LeftInvariantDerivation I G) (v : lieSmoothVectors I π) :
    wordSeminorm I π b k (lieSmoothVectorsDerivative I π Y v) ≤
      (∑ i, |b.repr Y i|) * wordSeminorm I π b (k + 1) v :=
  wordSeminorm_lieSmoothVectorsDerivative_le_of_eq_sum b k _ (b.sum_repr Y).symm v

end RealCombination

/-- **The word seminorms of the trivial representation are the norm**: `P_k(v) = ‖v‖` for every
`k`, since only the empty word acts nontrivially. -/
@[simp]
theorem wordSeminorm_trivial (X : ι → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I (trivial 𝕜 G V)) :
    wordSeminorm I (trivial 𝕜 G V) X k v = ‖(v : V)‖ := by
  rw [wordSeminorm_apply, Finset.sum_eq_single (⟨0, Fin.elim0⟩ : BoundedWord ι k)]
  · simp
  · rintro ⟨n, w⟩ - hw
    have hn : (n : ℕ) ≠ 0 := fun hn ↦ hw (by
      obtain rfl : n = 0 := Fin.ext hn
      exact congrArg _ (funext fun i ↦ i.elim0))
    have hne : List.ofFn w ≠ [] := by simpa [List.ofFn_eq_nil_iff] using hn
    simp [wordAction_trivial_of_ne_nil X hne]
  · simp

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

/-- **The Sobolev seminorms of the trivial representation are the norm**: `Q_k(v) = ‖v‖` for every
`k`, since only the constant monomial acts nontrivially. -/
@[simp]
theorem sobolevSeminorm_trivial (X : Fin m → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I (trivial 𝕜 G V)) :
    sobolevSeminorm I (trivial 𝕜 G V) X k v = ‖(v : V)‖ := by
  let α₀ : SobolevIndex m k := ⟨0, by simp⟩
  have hα₀ : α₀.exponent = 0 := funext fun _ ↦ by simp [α₀]
  rw [sobolevSeminorm_apply, Finset.sum_eq_single α₀]
  · simp [monomialWord_eq_nil_iff.mpr hα₀, Real.sqrt_sq (norm_nonneg _)]
  · intro α _ hα
    have hne : monomialWord α.exponent ≠ [] := by
      rw [Ne, monomialWord_eq_nil_iff, ← hα₀]
      exact SobolevIndex.exponent_injective.ne hα
    simp [wordAction_trivial_of_ne_nil X hne]
  · simp

/-- The Sobolev seminorm is bounded by the word seminorm: every ordered monomial is a word, and
the `ℓ²` norm of a finite family is at most its `ℓ¹` norm. -/
theorem sobolevSeminorm_le_wordSeminorm (X : Fin m → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) : sobolevSeminorm I π X k v ≤ wordSeminorm I π X k v := by
  classical
  set b : BoundedWord (Fin m) k → ℝ := fun w ↦ ‖(wordAction I π X (List.ofFn w.2) v : V)‖
  have hb : ∀ α : SobolevIndex m k,
      ‖(wordAction I π X (monomialWord α.exponent) v : V)‖ = b α.toBoundedWord := fun α ↦ by
    simp only [b, SobolevIndex.ofFn_toBoundedWord]
  have hsum : ∑ α : SobolevIndex m k, b α.toBoundedWord ≤ ∑ w, b w :=
    Finset.sum_le_sum_of_injOn SobolevIndex.toBoundedWord
      SobolevIndex.toBoundedWord_injective.injOn (Finset.subset_univ _) (fun _ _ ↦ le_rfl)
      fun _ _ _ ↦ norm_nonneg _
  rw [sobolevSeminorm_apply, wordSeminorm_apply, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, ?_⟩
  simp_rw [hb]
  calc ∑ α : SobolevIndex m k, b α.toBoundedWord ^ 2
    _ ≤ (∑ α : SobolevIndex m k, b α.toBoundedWord) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ (∑ w, b w) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hsum 2

end ContRepresentation
