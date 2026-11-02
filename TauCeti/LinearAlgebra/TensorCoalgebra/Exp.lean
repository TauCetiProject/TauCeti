/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Data.Nat.Choose.Cast
import TauCeti.LinearAlgebra.End.TensorProduct

/-!
# Exponentials of length-lowering coderivations

Let `φ : Tᶜ(M) ⟶ M` be a family of Taylor components with no unary component, over a
`ℚ`-algebra `R`.  The coderivation `D = coderiv φ` of the reduced tensor coalgebra collapses a block
of at least two letters to a single letter, so it strictly lowers tensor length and every word of
length at most `n` is killed by `Dⁿ`.  Its **exponential**

```text
exp D = ∑ Dʳ / r!
```

is therefore a finite sum on each word.  Since `D` satisfies the co-Leibniz rule
`Δ ∘ D = (D ⊗ 1 + 1 ⊗ D) ∘ Δ`, the binomial theorem for the commuting endomorphisms `D ⊗ 1` and
`1 ⊗ D` gives `Δ ∘ Dʳ = ∑ (r choose a) (Dᵃ ⊗ Dʳ⁻ᵃ) ∘ Δ`, and after division by `r!` this says that
`exp D` is a coalgebra endomorphism.  It fixes every single letter, so it is bijective
(`TauCeti.ReducedTensorWords.IsCoalgHom.bijective_of_comp_ofLetter_eq`), and it commutes with every
endomorphism commuting with `D`.

This is the exponential gauge of `A∞` structures over a `ℚ`-algebra: when `φ` is a Hochschild
cocycle of an `A∞` algebra that is homogeneous of degree zero for the shifted grading, `D` commutes
with the bar differential and `exp D` is an `A∞` automorphism.

## Main definitions

* `TauCeti.ReducedTensorWords.expCoderiv`: the exponential of the coderivation of `φ`.

## Main results

* `TauCeti.ReducedTensorWords.expCoderiv_apply_eq_sum` and
  `TauCeti.ReducedTensorWords.expCoderiv_apply_eq_sum_of_pow_apply_eq_zero`: on a word killed by
  `Dⁿ`, the exponential is the sum of the first `n` terms of its series.
* `TauCeti.ReducedTensorWords.deconcatenation_comp_pow_coderiv`: the binomial expansion
  `Δ ∘ Dʳ = ∑ (r choose a) (Dᵃ ⊗ Dʳ⁻ᵃ) ∘ Δ`, for any coderivation `D = coderiv φ`.
* `TauCeti.ReducedTensorWords.isCoalgHom_expCoderiv`: the exponential is a coalgebra morphism.
* `TauCeti.ReducedTensorWords.expCoderiv_comp_ofLetter`: it fixes single letters.
* `TauCeti.ReducedTensorWords.expCoderiv_apply_of_mem_filtration`: it is `id + D` on the words of
  length at most `2 e`, when `φ` vanishes on the words of length at most `e`.
* `TauCeti.ReducedTensorWords.commute_expCoderiv`: it commutes with every endomorphism commuting
  with `D`.
* `TauCeti.ReducedTensorWords.isHomogeneous_expCoderiv`: it has degree zero when `φ` does.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2,
  for coderivations of the bar construction.
* G. Freudenburg, *Algebraic Theory of Locally Nilpotent Derivations*, Encyclopaedia of
  Mathematical Sciences 136, Springer (2006), Chapter 1, for exponentials of locally nilpotent
  derivations, whose coalgebra version this is.
-/

public section

open scoped TensorProduct

universe uR uM

namespace TauCeti.ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-! ### Powers of a coderivation -/

/-- The binomial expansion of a power of a coderivation `D` against the deconcatenation:
`Δ ∘ Dʳ = ∑_{a + b = r} (r choose a) (Dᵃ ⊗ Dᵇ) ∘ Δ`. -/
theorem deconcatenation_comp_pow_coderiv {φ : ReducedTensorWords R M →ₗ[R] M} (r : ℕ) :
    deconcatenation R M ∘ₗ coderiv R φ ^ r =
      (∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 •
        TensorProduct.map (coderiv R φ ^ ij.1) (coderiv R φ ^ ij.2)) ∘ₗ deconcatenation R M := by
  set X : Module.End R (ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) :=
    LinearMap.rTensor (ReducedTensorWords R M) (coderiv R φ)
  set Y : Module.End R (ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) :=
    LinearMap.lTensor (ReducedTensorWords R M) (coderiv R φ)
  have hXY : Commute X Y := Module.End.commute_rTensor_lTensor _ _
  have hpow : deconcatenation R M ∘ₗ coderiv R φ ^ r = ((X + Y) ^ r) ∘ₗ deconcatenation R M := by
    induction r with
    | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id,
        LinearMap.comp_id, LinearMap.id_comp]
    | succ r ih =>
        rw [pow_succ', pow_succ', Module.End.mul_eq_comp, Module.End.mul_eq_comp,
          ← LinearMap.comp_assoc, isCoderivation_iff.1 (isCoderivation_coderiv R φ),
          LinearMap.comp_assoc, ih,
          LinearMap.comp_assoc]
  rw [hpow, hXY.add_pow']
  congr 1
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [LinearMap.rTensor_pow, LinearMap.lTensor_pow, Module.End.mul_eq_comp,
    LinearMap.rTensor_comp_lTensor]

/-! ### The exponential -/

variable [Algebra ℚ R]

variable (R) in
/-- The **exponential** `exp D = ∑ Dʳ / r!` of the coderivation `D = coderiv φ`, for Taylor
components `φ` with no unary component.  Such a `D` lowers tensor length, so on the words of
length `n` the terms with `r ≥ n` vanish and the series is truncated there; this truncation is the
definition, for an arbitrary `φ`. -/
noncomputable def expCoderiv (φ : ReducedTensorWords R M →ₗ[R] M) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦
    ∑ r ∈ Finset.range n.1, algebraMap ℚ R (r.factorial : ℚ)⁻¹ • ((coderiv R φ ^ r) ∘ₗ of R M n)

variable {φ : ReducedTensorWords R M →ₗ[R] M}

/-- **The exponential on a short word.**  On a word of length at most `n` the exponential of a
coderivation with no unary Taylor component is the sum of the first `n` terms of its series. -/
theorem expCoderiv_apply_eq_sum (hφ : φ ∘ₗ ofLetter R M = 0) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    expCoderiv R φ z =
      ∑ r ∈ Finset.range n, algebraMap ℚ R (r.factorial : ℚ)⁻¹ • (coderiv R φ ^ r) z := by
  have h : filtration R M n ≤ LinearMap.eqLocus (expCoderiv R φ)
      (∑ r ∈ Finset.range n, algebraMap ℚ R (r.factorial : ℚ)⁻¹ • coderiv R φ ^ r) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, expCoderiv, toModule_of]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    refine Finset.sum_subset (Finset.range_subset_range.2 hk) fun r _ hr ↦ ?_
    rw [Finset.mem_range, not_lt] at hr
    rw [Module.End.pow_map_zero_of_le hr
      (pow_coderiv_apply_eq_zero_of_mem_filtration R hφ (of_mem_filtration R M le_rfl x)),
      smul_zero]
  simpa only [LinearMap.mem_eqLocus, LinearMap.sum_apply, LinearMap.smul_apply] using h hz

/-- **The exponential on a word killed by a power.**  If `Dᵏ` kills `z`, for `D` a coderivation
with no unary Taylor component, then the exponential of `D` at `z` is the sum of the first `k`
terms of its series. -/
theorem expCoderiv_apply_eq_sum_of_pow_apply_eq_zero (hφ : φ ∘ₗ ofLetter R M = 0) {k : ℕ}
    {z : ReducedTensorWords R M} (hk : (coderiv R φ ^ k) z = 0) :
    expCoderiv R φ z =
      ∑ r ∈ Finset.range k, algebraMap ℚ R (r.factorial : ℚ)⁻¹ • (coderiv R φ ^ r) z := by
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  -- Both truncations agree with the truncation at `n + k`.
  have hext : ∀ m, (∀ r, m ≤ r → (coderiv R φ ^ r) z = 0) →
      ∑ r ∈ Finset.range m, algebraMap ℚ R (r.factorial : ℚ)⁻¹ • (coderiv R φ ^ r) z =
        ∑ r ∈ Finset.range (n + k), algebraMap ℚ R (r.factorial : ℚ)⁻¹ • (coderiv R φ ^ r) z := by
    intro m hm
    by_cases hmk : m ≤ n + k
    · refine Finset.sum_subset (Finset.range_subset_range.2 hmk) fun r _ hr ↦ ?_
      rw [Finset.mem_range, not_lt] at hr
      rw [hm r hr, smul_zero]
    · refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r _ hr ↦ ?_).symm
      rw [Finset.mem_range, not_lt] at hr
      rw [Module.End.pow_map_zero_of_le (by omega : k ≤ r) hk, smul_zero]
  rw [expCoderiv_apply_eq_sum hφ hn, hext n fun r hr ↦ Module.End.pow_map_zero_of_le hr
      (pow_coderiv_apply_eq_zero_of_mem_filtration R hφ hn),
    hext k fun r hr ↦ Module.End.pow_map_zero_of_le hr hk]

/-- The exponential of a coderivation with no unary Taylor component fixes single letters. -/
@[simp]
theorem expCoderiv_comp_ofLetter (hφ : φ ∘ₗ ofLetter R M = 0) :
    expCoderiv R φ ∘ₗ ofLetter R M = ofLetter R M := by
  refine LinearMap.ext fun a ↦ ?_
  rw [LinearMap.comp_apply, expCoderiv_apply_eq_sum hφ (ofLetter_mem_filtration R M a),
    Finset.sum_range_one, pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one,
    inv_one, map_one, one_smul]

/-- **The exponential to first order.**  If `φ` vanishes on the words of length at most `e`, for
some `e ≥ 1`, then the exponential of `D = coderiv φ` is `id + D` on the words of length at most
`2 e`: there `D ∘ D` vanishes, since each application of `D` shortens a word by at least `e`. -/
theorem expCoderiv_apply_of_mem_filtration {e : ℕ} (he : 1 ≤ e)
    (hφ : ∀ z ∈ filtration R M e, φ z = 0) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M (2 * e)) :
    expCoderiv R φ z = z + coderiv R φ z := by
  have hφ₁ : φ ∘ₗ ofLetter R M = 0 := LinearMap.ext fun a ↦
    hφ _ (filtration_monotone R M he (ofLetter_mem_filtration R M a))
  have hD : coderiv R φ z ∈ filtration R M e :=
    coderiv_filtration_add_le R φ hφ e ⟨z, by rwa [← two_mul], rfl⟩
  have hDD : (coderiv R φ ^ 2) z = 0 := by
    have h := coderiv_filtration_add_le R φ hφ 0 ⟨_, by rwa [zero_add], rfl⟩
    rw [filtration_zero, Submodule.mem_bot] at h
    rw [sq, Module.End.mul_apply, h]
  rw [expCoderiv_apply_eq_sum_of_pow_apply_eq_zero hφ₁ hDD, Finset.sum_range_succ,
    Finset.sum_range_one, pow_zero, pow_one, Module.End.one_apply]
  simp

/-- **The exponential commutes with what commutes with the coderivation.**  An endomorphism `T` of
the reduced tensor coalgebra commuting with a coderivation `D` with no unary Taylor component
commutes with its exponential.  No length condition on `T` is needed: `Dᵏ` kills `T z` as soon as
it kills `z`. -/
theorem commute_expCoderiv (hφ : φ ∘ₗ ofLetter R M = 0)
    {T : Module.End R (ReducedTensorWords R M)} (hT : Commute T (coderiv R φ)) :
    Commute T (expCoderiv R φ) := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  have hTr : ∀ r, T ((coderiv R φ ^ r) z) = (coderiv R φ ^ r) (T z) := fun r ↦ by
    rw [← Module.End.mul_apply, (hT.pow_right r).eq, Module.End.mul_apply]
  have hz := pow_coderiv_apply_eq_zero_of_mem_filtration R hφ hn
  have hTz : (coderiv R φ ^ n) (T z) = 0 := by rw [← hTr, hz, map_zero]
  rw [Module.End.mul_apply, Module.End.mul_apply, expCoderiv_apply_eq_sum hφ hn,
    expCoderiv_apply_eq_sum_of_pow_apply_eq_zero hφ hTz, map_sum]
  simp only [map_smul, hTr]

/-- **The exponential of a coderivation is a coalgebra morphism**, when the coderivation has no
unary Taylor component.  This is the binomial theorem for the commuting endomorphisms `D ⊗ 1` and
`1 ⊗ D` of `Tᶜ(M) ⊗ Tᶜ(M)`, divided by factorials. -/
theorem isCoalgHom_expCoderiv (hφ : φ ∘ₗ ofLetter R M = 0) :
    IsCoalgHom R (expCoderiv R φ) := by
  rw [isCoalgHom_iff]
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨N, hN⟩ := exists_mem_filtration R M z
  -- The truncation `S` of the exponential at `N`, and the summands `T` of its tensor square.
  let c : ℕ → R := fun r ↦ algebraMap ℚ R (r.factorial : ℚ)⁻¹
  let S : Module.End R (ReducedTensorWords R M) := ∑ r ∈ Finset.range N, c r • coderiv R φ ^ r
  let T : ℕ × ℕ → ReducedTensorWords R M ⊗[R] ReducedTensorWords R M := fun ij ↦
    (c ij.1 * c ij.2) •
      TensorProduct.map (coderiv R φ ^ ij.1) (coderiv R φ ^ ij.2) (deconcatenation R M z)
  have hkill : ∀ a, ∀ w ∈ filtration R M a, (coderiv R φ ^ a) w = 0 := fun _ _ hw ↦
    pow_coderiv_apply_eq_zero_of_mem_filtration R hφ hw
  -- The summands `T (a, b)` with `a ≥ N` or `b ≥ N` vanish.
  have hvan : ∀ a b, N ≤ a ∨ N ≤ b → T (a, b) = 0 := fun a b hab ↦ by
    simp only [T]
    rw [map_deconcatenation_eq_zero_of_mem_filtration R M (hkill a) (hkill b)
      (filtration_monotone R M (by omega) hN), smul_zero]
  -- On the cuts of `z`, which have length at most `N`, the exponential agrees with `S`.
  have hS : TensorProduct.map (expCoderiv R φ) (expCoderiv R φ) (deconcatenation R M z) =
      TensorProduct.map S S (deconcatenation R M z) := by
    obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M N
      ⟨z, filtration_monotone R M N.le_succ hN, rfl⟩
    rw [← hw]
    clear hw
    induction w using TensorProduct.inductionOn with
    | tmul u v =>
        simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype]
        rw [expCoderiv_apply_eq_sum hφ u.2, expCoderiv_apply_eq_sum hφ v.2]
        simp only [S, c, LinearMap.sum_apply, LinearMap.smul_apply]
    | add u v hu hv => simp only [map_add, hu, hv]
  -- The tensor square of `S` expands into the summands `T`.
  have hSS : TensorProduct.map S S (deconcatenation R M z) =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, T (a, b) := by
    simp only [T]
    generalize deconcatenation R M z = w
    induction w using TensorProduct.inductionOn with
    | tmul u v =>
        simp only [S, TensorProduct.map_tmul, LinearMap.sum_apply, LinearMap.smul_apply,
          TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul_smul]
        exact Finset.sum_comm
    | add u v hu hv => simp only [map_add, hu, hv, smul_add, Finset.sum_add_distrib]
  -- The binomial expansion of `Δ ∘ Dʳ`, divided by `r!`, gives the summands `T`.
  have hΔ : ∀ r, deconcatenation R M ((coderiv R φ ^ r) z) =
      ∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 •
        TensorProduct.map (coderiv R φ ^ ij.1) (coderiv R φ ^ ij.2) (deconcatenation R M z) :=
    fun r ↦ by
      rw [← LinearMap.comp_apply (deconcatenation R M), deconcatenation_comp_pow_coderiv,
        LinearMap.comp_apply, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hS, hSS,
    expCoderiv_apply_eq_sum hφ (filtration_monotone R M (by omega : N ≤ N + N) hN), map_sum,
    ← sum_range_add_antidiagonal_of_support N N T hvan]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_smul, hΔ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  rw [Finset.mem_antidiagonal] at hij
  subst hij
  simp only [T, c]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, ← map_natCast (algebraMap ℚ R), ← map_mul, ← map_mul,
    Nat.inv_factorial_mul_choose _ _ _ rfl]

end TauCeti.ReducedTensorWords

namespace TauCeti.ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [Algebra ℚ R] [AddCommMonoid M] [Module R M]

/-- The exponential of the coderivation of a degree-zero family of Taylor components with no unary
component has degree zero. -/
theorem isHomogeneous_expCoderiv (G : InternalGrading R M) {φ : ReducedTensorWords R M →ₗ[R] M}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece G) G.piece 0) (hφ₁ : φ ∘ₗ ofLetter R M = 0) :
    LinearMap.IsHomogeneous (expCoderiv R φ) (gradedPiece G) (gradedPiece G) 0 := by
  have hD : LinearMap.IsHomogeneous (coderiv R φ) (gradedPiece G) (gradedPiece G) 0 := by
    simpa only [gradedCoderiv_zero] using isHomogeneous_gradedCoderiv G φ 0 0 hφ
  rw [LinearMap.isHomogeneous_def] at hD ⊢
  intro p z hz
  rw [add_zero]
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  have hpow : ∀ r, (coderiv R φ ^ r) z ∈ gradedPiece G p := fun r ↦ by
    induction r with
    | zero => rwa [pow_zero, Module.End.one_apply]
    | succ r ih =>
        rw [pow_succ', Module.End.mul_apply]
        simpa only [add_zero] using hD p _ ih
  rw [expCoderiv_apply_eq_sum hφ₁ hn]
  exact Submodule.sum_mem _ fun r _ ↦ Submodule.smul_mem _ _ (hpow r)

end TauCeti.ReducedTensorWords
