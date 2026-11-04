/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.Probability.FreeProbability.Distribution.Basic
public import TauCeti.Probability.FreeProbability.Semicircular.Basic

/-!
# Semicircular systems

Let `φ : A →ₗ[R] R` be a linear functional on an algebra `A` over a commutative ring `R`. A family
`s : ι → A` is a *semicircular system with covariance `C : Matrix ι ι R`* for `φ` when `φ` is
normalised and the only nonvanishing joint free cumulants of the family are those of order two,
given by the covariance: `κ₂(s i, s j) = C i j`, and `κ_n(s_{w 1}, …, s_{w n}) = 0` for every word
`w` of length `n ≠ 2`. Equivalently, `φ (s i) = 0`, `φ (s i * s j) = C i j`, and all higher joint
free cumulants vanish. This is the free analogue of a centred Gaussian family with covariance `C`.

The joint distribution of a semicircular system is determined by its covariance, and every member
`s i` is semicircular of variance `C i i`. Real (or `R`-linear) changes of coordinates preserve
semicircular systems: if `t k = ∑ i, M i k • s i`, then `t` is a semicircular system with covariance
`Mᵀ * C * M`.

Semicircularity of each member does not determine the joint distribution; for a semicircular
system, freeness is the same as orthogonality. A semicircular system is freely independent exactly
when its covariance is diagonal, and a family is a semicircular system with diagonal covariance
`v` exactly when it is a free family of semicircular elements of variances `v i`. In particular,
a single element is a semicircular system exactly when it is semicircular.

No positivity, symmetry of `C`, or traciality of `φ` is assumed.

## Main definitions

* `TauCeti.IsSemicircularSystem φ s C` — `s` is a semicircular system with covariance `C` for `φ`.

## Main results

* `TauCeti.IsSemicircularSystem.apply_eq_zero`, `TauCeti.IsSemicircularSystem.apply_mul` — the
  members are centred, with second moments `φ (s i * s j) = C i j`.
* `TauCeti.IsSemicircularSystem.isSemicircular` — each member `s i` is semicircular of variance
  `C i i`.
* `TauCeti.IsSemicircularSystem.jointDistribution_eq` — the joint distribution of a semicircular
  system is determined by its covariance.
* `TauCeti.IsSemicircularSystem.comp` and `TauCeti.IsSemicircularSystem.sum_smul` — relabelling
  and linear changes of coordinates, with covariances `C.submatrix e e` and `Mᵀ * C * M`.
* `TauCeti.IsSemicircularSystem.isFreelyIndependentElements_iff` — a semicircular system is
  freely independent exactly when its covariance is diagonal.
* `TauCeti.isSemicircularSystem_diagonal_iff` — the semicircular systems with diagonal covariance
  `v` are the free families of semicircular elements of variances `v i`.
* `TauCeti.isSemicircularSystem_iff_isSemicircular` — a family indexed by a one-element type is a
  semicircular system exactly when its member is semicircular.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Definition 8.15 for
  semicircular families and Lecture 11 (Theorem 11.20 for the generated-algebra test).
-/

public section

open Finset Matrix

namespace TauCeti

variable {R A B ι κ : Type*} [CommRing R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  {φ : A →ₗ[R] R} {s : ι → A} {C : Matrix ι ι R}

/-- A family `s` is a *semicircular system with covariance `C`* for the functional `φ` if `φ` is
normalised and the only nonvanishing joint free cumulants of `s` are those of order two,
`κ₂(s i, s j) = C i j`. -/
structure IsSemicircularSystem (φ : A →ₗ[R] R) (s : ι → A) (C : Matrix ι ι R) : Prop where
  /-- The functional is normalised. -/
  apply_one : φ 1 = 1
  /-- The second joint free cumulants are given by the covariance. -/
  freeCumulant_two (w : Fin 2 → ι) : freeCumulant φ (s ∘ w) univ = C (w 0) (w 1)
  /-- The joint free cumulants of every order `n ≠ 2`, `n ≥ 1`, vanish. -/
  freeCumulant_eq_zero {n : ℕ} (hn₀ : n ≠ 0) (hn₂ : n ≠ 2) (w : Fin n → ι) :
    freeCumulant φ (s ∘ w) univ = 0

namespace IsSemicircularSystem

/-- The members of a semicircular system are centred. -/
theorem apply_eq_zero (h : IsSemicircularSystem φ s C) (i : ι) : φ (s i) = 0 := by
  simpa [univ_unique] using h.freeCumulant_eq_zero one_ne_zero (by decide) fun _ => i

/-- The second moments of a semicircular system are given by its covariance,
`φ (s i * s j) = C i j`. -/
theorem apply_mul (h : IsSemicircularSystem φ s C) (i j : ι) : φ (s i * s j) = C i j := by
  have hκ := h.freeCumulant_two ![i, j]
  rw [show (univ : Finset (Fin 2)) = {0, 1} by decide,
    freeCumulant_pair φ _ (show (0 : Fin 2) < 1 by decide)] at hκ
  simpa [h.apply_eq_zero] using hκ

/-- The joint free cumulants of a semicircular system depend only on its covariance: two
semicircular systems with the same covariance, possibly in different algebras, have the same joint
free cumulant along every word `w`, including the empty word. -/
theorem freeCumulant_comp_eq {φ' : B →ₗ[R] R} {t : ι → B} (h : IsSemicircularSystem φ s C)
    (h' : IsSemicircularSystem φ' t C) {n : ℕ} (w : Fin n → ι) :
    freeCumulant φ (s ∘ w) univ = freeCumulant φ' (t ∘ w) univ := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp [univ_eq_empty, freeCumulant_empty]
  rcases eq_or_ne n 2 with rfl | hn₂
  · rw [h.freeCumulant_two, h'.freeCumulant_two]
  · rw [h.freeCumulant_eq_zero hn₀ hn₂, h'.freeCumulant_eq_zero hn₀ hn₂]

/-- *The covariance determines the joint distribution*: two semicircular systems with the same
covariance, possibly in different algebras, have the same joint distribution. -/
theorem jointDistribution_eq {φ' : B →ₗ[R] R} {t : ι → B} (h : IsSemicircularSystem φ s C)
    (h' : IsSemicircularSystem φ' t C) : jointDistribution φ s = jointDistribution φ' t := by
  refine jointDistribution_eq_iff.2 fun w => ?_
  rcases eq_or_ne w.length 0 with hw | hw
  · simp [List.length_eq_zero_iff.1 hw, h.apply_one, h'.apply_one]
  -- Expand both moments by the moment–cumulant formula; the cumulants of every part agree.
  rw [← List.ofFn_getElem_eq_map, ← List.ofFn_getElem_eq_map,
    apply_prod_ofFn_eq_sum_prod_freeCumulant φ hw, apply_prod_ofFn_eq_sum_prod_freeCumulant φ' hw]
  refine sum_congr rfl fun π _ => prod_congr rfl fun X _ => ?_
  rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ _ X,
    freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ' _ X]
  exact h.freeCumulant_comp_eq h' fun k => w[(X.orderEmbOfFin rfl k : ℕ)]

/-- Each member `s i` of a semicircular system is semicircular of variance `C i i`. -/
theorem isSemicircular (h : IsSemicircularSystem φ s C) (i : ι) :
    IsSemicircular φ (s i) (C i i) := by
  refine (isSemicircular_iff_freeCumulant_const h.apply_one).2 fun n hn => ?_
  rcases eq_or_ne n 2 with rfl | hn₂
  · simpa [Function.comp_def] using h.freeCumulant_two fun _ => i
  · simpa [Function.comp_def, hn₂] using h.freeCumulant_eq_zero hn hn₂ fun _ => i

/-- *Relabelling*: a relabelled family `s ∘ e`, in particular a subfamily, of a semicircular
system with covariance `C` is a semicircular system with covariance `C.submatrix e e`. -/
theorem comp (h : IsSemicircularSystem φ s C) (e : κ → ι) :
    IsSemicircularSystem φ (s ∘ e) (C.submatrix e e) where
  apply_one := h.apply_one
  freeCumulant_two w := h.freeCumulant_two (e ∘ w)
  freeCumulant_eq_zero hn₀ hn₂ w := h.freeCumulant_eq_zero hn₀ hn₂ (e ∘ w)

/-- The joint free cumulants of the linear combinations `t k = ∑ i, M i k • s i` along a word `w`,
expanded by multilinearity over all words `v` in the original family. -/
private theorem freeCumulant_sum_smul [Fintype ι] (M : Matrix ι κ R) {n : ℕ}
    (w : Fin n → κ) :
    freeCumulant φ ((fun k => ∑ i, M i k • s i) ∘ w) univ =
      ∑ v : Fin n → ι, (∏ m, M (v m) (w m)) * freeCumulant φ (s ∘ v) univ := by
  classical
  simp_rw [← freeCumulantMultilinear_apply, Function.comp_def, MultilinearMap.map_sum,
    MultilinearMap.map_smul_univ, smul_eq_mul]

/-- *Linear changes of coordinates*: if `s` is a semicircular system with covariance `C` and `M`
is a matrix, then the linear combinations `t k = ∑ i, M i k • s i` form a semicircular system with
covariance `Mᵀ * C * M`. -/
theorem sum_smul [Fintype ι] (h : IsSemicircularSystem φ s C) (M : Matrix ι κ R) :
    IsSemicircularSystem φ (fun k => ∑ i, M i k • s i) (Mᵀ * C * M) where
  apply_one := h.apply_one
  freeCumulant_two w := by
    classical
    rw [freeCumulant_sum_smul, ← (finTwoArrowEquiv ι).symm.sum_comp, Fintype.sum_prod_type]
    simp only [h.freeCumulant_two, finTwoArrowEquiv_symm_apply, Fin.prod_univ_two,
      cons_val_zero, cons_val_one, Matrix.mul_apply, transpose_apply, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  freeCumulant_eq_zero hn₀ hn₂ w := by
    classical
    simp [freeCumulant_sum_smul, h.freeCumulant_eq_zero hn₀ hn₂]

/-- *Freeness is orthogonality*: a semicircular system is freely independent exactly when its
covariance is diagonal. -/
theorem isFreelyIndependentElements_iff (h : IsSemicircularSystem φ s C) :
    IsFreelyIndependentElements φ s ↔ ∀ i j, i ≠ j → C i j = 0 := by
  rw [isFreelyIndependentElements_iff_freeCumulant_eq_zero h.apply_one]
  refine ⟨fun hfree i j hij => ?_, fun hC n w k k' hkk' => ?_⟩
  · simpa [h.freeCumulant_two] using hfree 2 ![i, j] 0 1 hij
  -- Only the cumulants of order two can be mixed, and these are off-diagonal entries of `C`.
  rcases eq_or_ne n 2 with rfl | hn₂
  · rw [h.freeCumulant_two]
    refine hC _ _ fun h01 => hkk' ?_
    fin_cases k <;> fin_cases k' <;> simp [h01]
  · exact h.freeCumulant_eq_zero (fun hn => (Fin.cast hn k).elim0) hn₂ w

end IsSemicircularSystem

/-- *Free semicircular families*: a family `s` is a semicircular system with diagonal covariance
`diagonal v` for `φ` exactly when `φ` is normalised and the `s i` are freely independent
semicircular elements of variances `v i`. -/
theorem isSemicircularSystem_diagonal_iff [DecidableEq ι] {v : ι → R} :
    IsSemicircularSystem φ s (diagonal v) ↔
      φ 1 = 1 ∧ IsFreelyIndependentElements φ s ∧ ∀ i, IsSemicircular φ (s i) (v i) := by
  refine ⟨fun h => ⟨h.apply_one, h.isFreelyIndependentElements_iff.2 fun i j hij =>
    diagonal_apply_ne v hij, fun i => by simpa using h.isSemicircular i⟩,
    fun ⟨hφ, hfree, hs⟩ => ?_⟩
  -- A constant word has the cumulants of one semicircular element; any other word is mixed.
  have hκ {n : ℕ} (hn₀ : n ≠ 0) (w : Fin n → ι) :
      freeCumulant φ (s ∘ w) univ = if n = 2 ∧ ∀ m, w m = w ⟨0, by omega⟩ then v (w ⟨0, by omega⟩)
        else 0 := by
    by_cases hw : ∀ m, w m = w ⟨0, by omega⟩
    · have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      rw [show s ∘ w = fun _ => s (w ⟨0, by omega⟩) from funext fun m => congrArg s (hw m),
        (hs _).freeCumulant_const univ_nonempty]
      simp [hw]
    · push Not at hw
      obtain ⟨m, hm⟩ := hw
      have hw : ¬(n = 2 ∧ ∀ m, w m = w ⟨0, by omega⟩) := fun h' => hm (h'.2 m)
      simp only [hw, ↓reduceIte]
      exact (isFreelyIndependentElements_iff_freeCumulant_eq_zero hφ).1 hfree n w m _ hm
  refine ⟨hφ, fun w => ?_, fun hn₀ hn₂ w => by simp [hκ hn₀, hn₂]⟩
  rw [hκ two_ne_zero]
  by_cases h01 : w 1 = w 0
  · simp [Fin.forall_fin_two, h01]
  · simp [Fin.forall_fin_two, h01, diagonal_apply_ne v (Ne.symm h01)]

/-- A single element is a semicircular system, with the `1 × 1` covariance given by its variance,
exactly when it is semicircular. -/
theorem isSemicircularSystem_iff_isSemicircular [Unique ι] :
    IsSemicircularSystem φ s C ↔ IsSemicircular φ (s default) (C default default) := by
  classical
  have hC : C = diagonal fun i => C i i := by
    ext i j
    simp [Subsingleton.elim i j]
  rw [hC, isSemicircularSystem_diagonal_iff]
  exact ⟨fun h => h.2.2 default, fun h => ⟨h.apply_one,
    isFreelyIndependentElements_of_subsingleton φ s, fun i => Unique.eq_default i ▸ h⟩⟩

end TauCeti
