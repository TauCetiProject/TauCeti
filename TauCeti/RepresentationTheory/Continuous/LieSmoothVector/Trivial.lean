/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Seminorm

/-!
# Smooth vectors of the trivial representation

For the trivial continuous representation `ContRepresentation.trivial R G V` of a real Lie group
`G` on a normed space `V`, every orbit map is constant, so every vector is smooth
(`ContRepresentation.lieSmoothVectors_trivial`) and every derivative of positive order vanishes:
`dπ(X) = 0` (`ContRepresentation.lieSmoothVectorsDerivative_trivial`), so `dπ(X_w) = 0` for every
nonempty word `w` (`ContRepresentation.wordAction_trivial_of_ne_nil`). Hence the word seminorms
`P_k` and the Sobolev seminorms `Q_k` of every order are the norm of `V`
(`ContRepresentation.wordSeminorm_trivial`, `ContRepresentation.sobolevSeminorm_trivial`), so
both families of seminorms define the norm topology on `V`.

## Main results

* `ContRepresentation.lieSmoothVectors_trivial`: every vector of the trivial representation is
  smooth.
* `ContRepresentation.lieSmoothVectorsDerivative_trivial`: its derived action is zero.
* `ContRepresentation.wordSeminorm_trivial`, `ContRepresentation.sobolevSeminorm_trivial`:
  `P_k = Q_k = ‖·‖`.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.4.
-/

public section

noncomputable section

open TauCeti
open scoped ContDiff Manifold

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {R : Type*} [Ring R] [Module R V]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- Every vector of the trivial representation is smooth: its orbit map is constant. -/
theorem isLieSmoothVector_trivial (v : V) : IsLieSmoothVector I (trivial R G V) v := by
  rw [isLieSmoothVector_iff]
  simpa only [trivial_apply] using (contMDiff_const : ContMDiff I 𝓘(ℝ, V) ∞ fun _ : G ↦ v)

/-- **Every vector of the trivial representation is smooth.** -/
@[simp]
theorem lieSmoothVectors_trivial [SMulCommClass ℝ R V] [ContinuousConstSMul R V] :
    lieSmoothVectors I (trivial R G V) = ⊤ :=
  eq_top_iff.mpr fun v _ ↦ (mem_lieSmoothVectors I _).mpr (isLieSmoothVector_trivial I v)

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

variable {I} in
/-- The derived action of the trivial representation vanishes. -/
@[simp]
theorem lieDerivative_trivial (X : LeftInvariantDerivation I G) (v : V) :
    lieDerivative (trivial R G V) X v = 0 := by
  simp only [lieDerivative_def, trivial_apply, deriv_const]

variable [SMulCommClass ℝ R V] [ContinuousConstSMul R V]

/-- **The derived action of the trivial representation on its smooth vectors is zero.** -/
@[simp]
theorem lieSmoothVectorsDerivative_trivial (X : LeftInvariantDerivation I G) :
    lieSmoothVectorsDerivative I (trivial R G V) X = 0 :=
  LinearMap.ext fun w ↦ Subtype.ext (by simp)

/-- For the trivial representation, every nonempty word acts by zero. -/
theorem wordAction_trivial_of_ne_nil {ι : Type*} (X : ι → LeftInvariantDerivation I G)
    {w : List ι} (hw : w ≠ []) : wordAction I (trivial R G V) X w = 0 := by
  obtain ⟨i, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]

/-- **The word seminorms of the trivial representation are the norm**: `P_k(v) = ‖v‖` for every
`k`, since only the empty word acts nontrivially. -/
@[simp]
theorem wordSeminorm_trivial {ι : Type*} [Fintype ι] (X : ι → LeftInvariantDerivation I G)
    (k : ℕ) (v : lieSmoothVectors I (trivial 𝕜 G V)) :
    wordSeminorm I (trivial 𝕜 G V) X k v = ‖(v : V)‖ := by
  rw [wordSeminorm_apply, Finset.sum_eq_single (⟨0, Fin.elim0⟩ : BoundedWord ι k)]
  · simp
  · rintro ⟨n, w⟩ - hw
    have hn : (n : ℕ) ≠ 0 := fun hn ↦ hw (by
      obtain rfl : n = 0 := Fin.ext hn
      exact congrArg _ (funext fun i ↦ i.elim0))
    have hne : List.ofFn w ≠ [] := by simpa [List.ofFn_eq_nil_iff] using hn
    simp [wordAction_trivial_of_ne_nil I X hne]
  · simp

/-- **The Sobolev seminorms of the trivial representation are the norm**: `Q_k(v) = ‖v‖` for every
`k`, since only the constant monomial acts nontrivially. -/
@[simp]
theorem sobolevSeminorm_trivial {m : ℕ} (X : Fin m → LeftInvariantDerivation I G) (k : ℕ)
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
    simp [wordAction_trivial_of_ne_nil I X hne]
  · simp

end ContRepresentation
