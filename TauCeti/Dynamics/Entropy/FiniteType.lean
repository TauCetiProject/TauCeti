/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Dynamics.Entropy.Language
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import TauCeti.Analysis.Asymptotics.ExpGrowth
import TauCeti.LinearAlgebra.Eigenspace.Matrix
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Nonnegative

/-!
# Topological entropy of one-step subshifts of finite type

For a finite alphabet `α` and a `0`-`1` transition matrix `M : Matrix α α ℝ`, the one-step
subshift of finite type `TauCeti.sftSet M ⊆ ℕ → α` consists of the sequences `x` with
`M (x k) (x (k + 1)) = 1` for every `k`. If no row of `M` is zero, its topological entropy under
the shift is `log` of the spectral radius of `M`:

```text
coverEntropy (shift 1) (sftSet M) = log (spectralRadius ℝ M).
```

The proof counts admissible words by entries of powers of `M`, as the roadmap suggests. The
products `∏ k, M (w k) (w (k + 1))` over words `w` of length `n + 1` starting at `i` sum to
`(M ^ n *ᵥ 1) i`, and for a `0`-`1` matrix such a product is the indicator of admissibility; if no
row is zero, every admissible word extends to a point of `sftSet M`, so the number of words of
length `n + 1` read off `sftSet M` is `∑ i, (M ^ n *ᵥ 1) i`. Its growth rate is at most
`log ρ` by Gelfand's formula for the `L∞` operator norm, and at least `log ρ` by the
Perron–Frobenius theorem for nonnegative matrices (`Matrix.exists_mulVec_eq_smul_of_nonneg`): a
nonzero nonnegative eigenvector `v` for the spectral radius `ρ` gives
`ρ ^ n ∑ v ≤ (max v) ∑ i, (M ^ n *ᵥ 1) i`. That theorem also shows that the real and complex
spectral radii of a nonnegative matrix agree.

## Main definitions

* `TauCeti.sftSet M`: the one-step subshift of finite type with transition matrix `M`.
* `TauCeti.pathWeight M w`: the product `∏ k, M (w k) (w (k + 1))` along a word `w`.

## Main results

* `TauCeti.sum_pathWeight_cons`: the path weights of words starting at `i` sum to
  `(M ^ n *ᵥ 1) i`.
* `TauCeti.languageCount_sftSet`: the number of words of length `n + 1` read off `sftSet M` is
  `∑ i, (M ^ n *ᵥ 1) i`.
* `TauCeti.expGrowthSup_eq_log_of_tendsto_rpow`: a sequence `u` with `u n ^ (1 / n) → a` has
  exponential growth rate `log a`.
* `Matrix.spectralRadius_real_eq_of_nonneg`: a nonnegative real matrix has the same spectral radius
  over `ℝ` and over `ℂ`.
* `TauCeti.coverEntropy_shift_sftSet`: the entropy formula.

This is the subshift-of-finite-type part of item 4 of §5.2 of the ClassicalErgodicTheory roadmap.
-/

public section

open Dynamics Set Filter ExpGrowth SymbolicDynamics.FullShift Topology
open scoped Matrix ENNReal NNReal

namespace TauCeti

section Growth

/-- A sequence `u` of extended nonnegative reals with `u n ^ (1 / n) → a` has exponential growth
rate `log a`. -/
theorem expGrowthSup_eq_log_of_tendsto_rpow {u : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (h : Tendsto (fun n : ℕ ↦ u n ^ (1 / n : ℝ)) atTop (𝓝 a)) :
    expGrowthSup u = ENNReal.log a := by
  have h' := (ENNReal.continuous_log.tendsto a).comp h
  rw [expGrowthSup_def, LinearGrowth.linearGrowthSup]
  refine (limsup_congr (Eventually.of_forall fun n ↦ ?_)).trans h'.limsup_eq
  simp only [Function.comp_apply, ENNReal.log_rpow]
  rw [EReal.div_eq_inv_mul, one_div, EReal.coe_inv, EReal.coe_natCast]

end Growth

variable {α : Type*}

/-- The one-step subshift of finite type with transition matrix `M`: the sequences `x` with
`M (x k) (x (k + 1)) = 1` for every `k`. -/
def sftSet (M : Matrix α α ℝ) : Set (ℕ → α) :=
  {x | ∀ k, M (x k) (x (k + 1)) = 1}

theorem mem_sftSet {M : Matrix α α ℝ} {x : ℕ → α} :
    x ∈ sftSet M ↔ ∀ k, M (x k) (x (k + 1)) = 1 :=
  Iff.rfl

/-- The shift maps a subshift of finite type into itself. -/
theorem mapsTo_shift_sftSet (M : Matrix α α ℝ) :
    MapsTo (shift (1 : ℕ)) (sftSet M) (sftSet M) := by
  intro x hx k
  simpa [shift_apply, add_assoc] using hx (1 + k)

/-- The product `∏ k, M (w k) (w (k + 1))` along a word `w` of length `n + 1`. -/
noncomputable def pathWeight (M : Matrix α α ℝ) {n : ℕ} (w : Fin (n + 1) → α) : ℝ :=
  ∏ k : Fin n, M (w k.castSucc) (w k.succ)

theorem pathWeight_def (M : Matrix α α ℝ) {n : ℕ} (w : Fin (n + 1) → α) :
    pathWeight M w = ∏ k : Fin n, M (w k.castSucc) (w k.succ) :=
  (rfl)

theorem pathWeight_cons (M : Matrix α α ℝ) {n : ℕ} (i : α) (w : Fin (n + 1) → α) :
    pathWeight M (Fin.cons i w : Fin (n + 2) → α) = M i (w 0) * pathWeight M w := by
  simp only [pathWeight_def, Fin.prod_univ_succ]
  congr 1

/-- For a `0`-`1` matrix the path weight of a word is the indicator of its admissibility. -/
theorem pathWeight_eq_ite {M : Matrix α α ℝ} (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) {n : ℕ}
    (w : Fin (n + 1) → α) [Decidable (∀ k : Fin n, M (w k.castSucc) (w k.succ) = 1)] :
    pathWeight M w = if ∀ k : Fin n, M (w k.castSucc) (w k.succ) = 1 then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one fun k _ ↦ h k
  · push Not at h
    obtain ⟨k, hk⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ k) ((h01 _ _).resolve_right hk)

/-- If no row of `M` is zero, every admissible word extends to a point of `sftSet M`. -/
theorem exists_mem_sftSet_of_admissible {M : Matrix α α ℝ} (hrow : ∀ i, ∃ j, M i j = 1) {n : ℕ}
    {w : Fin (n + 1) → α} (hw : ∀ k : Fin n, M (w k.castSucc) (w k.succ) = 1) :
    ∃ x ∈ sftSet M, ∀ i : Fin (n + 1), x i = w i := by
  choose f hf using hrow
  let x : ℕ → α := fun k ↦
    if h : k ≤ n then w ⟨k, Nat.lt_succ_of_le h⟩ else f^[k - n] (w (Fin.last n))
  have hx : ∀ k, n ≤ k → x k = f^[k - n] (w (Fin.last n)) := by
    intro k hk
    by_cases h : k ≤ n
    · have hkn : k = n := le_antisymm h hk
      subst hkn
      simp only [x, dite_eq_left h, Nat.sub_self, Function.iterate_zero, id]
      rfl
    · exact dite_eq_right h
  refine ⟨x, fun k ↦ ?_, fun i ↦ dite_eq_left (Nat.le_of_lt_succ i.isLt)⟩
  by_cases hk : k < n
  · rw [show x k = w (⟨k, hk⟩ : Fin n).castSucc from dite_eq_left hk.le,
      show x (k + 1) = w (⟨k, hk⟩ : Fin n).succ from dite_eq_left hk]
    exact hw _
  · rw [hx k (by omega), hx (k + 1) (by omega), show k + 1 - n = k - n + 1 by omega,
      Function.iterate_succ_apply']
    exact hf _

variable [Fintype α] [DecidableEq α]

/-- The path weights of the words of length `n + 1` starting at `i` sum to `(M ^ n *ᵥ 1) i`. -/
theorem sum_pathWeight_cons (M : Matrix α α ℝ) (n : ℕ) (i : α) :
    ∑ w : Fin n → α, pathWeight M (Fin.cons i w : Fin (n + 1) → α) = (M ^ n *ᵥ 1) i := by
  induction n generalizing i with
  | zero => simp [pathWeight_def]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct,
      ← Fintype.sum_equiv (Fin.consEquiv fun _ ↦ α) (fun p ↦ pathWeight M
        (Fin.cons i (Fin.cons p.1 p.2 : Fin (n + 1) → α) : Fin (n + 2) → α)) _ fun _ ↦ rfl,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [pathWeight_cons, Fin.cons_zero, ← Finset.mul_sum, ih]

/-- All path weights of words of length `n + 1` sum to `∑ i, (M ^ n *ᵥ 1) i`. -/
theorem sum_pathWeight (M : Matrix α α ℝ) (n : ℕ) :
    ∑ w : Fin (n + 1) → α, pathWeight M w = ∑ i, (M ^ n *ᵥ 1) i := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ ↦ α) (fun p ↦ pathWeight M
      (Fin.cons p.1 p.2 : Fin (n + 1) → α)) _ fun _ ↦ rfl, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ ↦ sum_pathWeight_cons M n i

/-- For a `0`-`1` matrix without zero rows, the words of length `n + 1` read off `sftSet M` are
counted by `∑ i, (M ^ n *ᵥ 1) i`. -/
theorem languageCount_sftSet {M : Matrix α α ℝ} (h01 : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hrow : ∀ i, ∃ j, M i j = 1) (n : ℕ) :
    (languageCount (sftSet M) (n + 1) : ℝ) = ∑ i, (M ^ n *ᵥ 1) i := by
  classical
  have hwords : wordsOf (sftSet M) (n + 1) =
      ((Finset.univ.filter fun w : Fin (n + 1) → α ↦
        ∀ k : Fin n, M (w k.castSucc) (w k.succ) = 1 : Finset _) : Set (Fin (n + 1) → α)) := by
    ext w
    simp only [mem_wordsOf, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq]
    refine ⟨fun ⟨x, hx, hxw⟩ k ↦ ?_, fun hw ↦ exists_mem_sftSet_of_admissible hrow hw⟩
    rw [← hxw, ← hxw]
    exact hx k
  rw [languageCount_def, hwords, ncard_coe_finset, ← sum_pathWeight, Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun w _ ↦ (pathWeight_eq_ite h01 w).symm

end TauCeti

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A nonnegative real square matrix has the same spectral radius over `ℝ` as over `ℂ`. -/
theorem spectralRadius_real_eq_of_nonneg [Nonempty n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    spectralRadius ℝ A = spectralRadius ℂ (A.map (↑) : Matrix n n ℂ) := by
  classical
  obtain ⟨r, hr, hρ, v, -, hv0, hAv⟩ := exists_mulVec_eq_smul_of_nonneg hA
  rw [hρ, spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun μ hμ ↦ ?_) ?_
  · obtain ⟨z, hz, hAz⟩ := mem_spectrum_iff_exists_mulVec_eq_smul.1 hμ
    have hz' : (fun i ↦ (z i : ℂ)) ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
      exact fun h ↦ hj (by simpa using congrFun h j)
    have hAz' : A.map (↑) *ᵥ (fun i ↦ (z i : ℂ)) = (μ : ℂ) • fun i ↦ (z i : ℂ) := by
      ext i
      simpa [mulVec, dotProduct] using congrArg Complex.ofReal (congrFun hAz i)
    have hmem : (μ : ℂ) ∈ spectrum ℂ (A.map (↑) : Matrix n n ℂ) :=
      mem_spectrum_iff_exists_mulVec_eq_smul.2 ⟨_, hz', hAz'⟩
    have := le_iSup₂ (f := fun (k : ℂ) (_ : k ∈ spectrum ℂ (A.map (↑) : Matrix n n ℂ)) ↦ ‖k‖ₑ)
      (μ : ℂ) hmem
    rw [← spectralRadius_eq_of_unital, hρ] at this
    simpa [eNorm_eq_nnNorm, Complex.nnNorm_real] using this
  · refine le_iSup₂_of_le r (mem_spectrum_iff_exists_mulVec_eq_smul.2 ⟨v, hv0, hAv⟩) ?_
    rw [Real.eNorm_eq_ofReal hr]

end Matrix

namespace TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The word sums `∑ i, (M ^ n *ᵥ 1) i` of a nonnegative matrix grow at most like the spectral
radius. -/
theorem expGrowthSup_sum_pow_mulVec_le {M : Matrix α α ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    expGrowthSup (fun n ↦ ENNReal.ofReal (∑ i, (M ^ n *ᵥ 1) i)) ≤
      ENNReal.log (spectralRadius ℂ (M.map (↑) : Matrix α α ℂ)) := by
  let := Matrix.linftyOpNormedRing (n := α) (α := ℂ)
  let := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := α) (α := ℂ)
  set N : Matrix α α ℂ := M.map (↑)
  have hpow (k : ℕ) : N ^ k = (M ^ k).map (↑) :=
    (map_pow (Complex.ofRealHom.mapMatrix) M k).symm
  have hbound (k : ℕ) : ENNReal.ofReal (∑ i, (M ^ k *ᵥ 1) i) ≤
      (Fintype.card α : ℝ≥0∞) * (‖N ^ k‖₊ : ℝ≥0∞) := by
    have hrow (i : α) : (M ^ k *ᵥ 1) i ≤ ‖N ^ k‖ := by
      calc (M ^ k *ᵥ 1) i = ∑ j, ‖(N ^ k) i j‖ := by
            simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, hpow, Matrix.map_apply,
              Complex.norm_real, Real.norm_eq_abs]
            exact Finset.sum_congr rfl fun j _ ↦
              (abs_of_nonneg (Matrix.pow_apply_nonneg hM k i j)).symm
        _ ≤ ‖N ^ k‖ := by
            rw [Matrix.linfty_opNorm_def]
            refine (by push_cast; rfl : ∑ j, ‖(N ^ k) i j‖ =
              ((∑ j, ‖(N ^ k) i j‖₊ : ℝ≥0) : ℝ)).trans_le (NNReal.coe_le_coe.2 ?_)
            exact Finset.le_sup (f := fun i ↦ ∑ j, ‖(N ^ k) i j‖₊) (Finset.mem_univ i)
    calc ENNReal.ofReal (∑ i, (M ^ k *ᵥ 1) i) ≤ ENNReal.ofReal (Fintype.card α * ‖N ^ k‖) := by
          gcongr
          simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hrow i
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ofReal_norm,
            eNorm_eq_nnNorm]
  calc _ ≤ expGrowthSup fun k ↦ (‖N ^ k‖₊ : ℝ≥0∞) :=
        expGrowthSup_le_of_eventually_le (ENNReal.natCast_ne_top _) (Eventually.of_forall hbound)
    _ = _ := expGrowthSup_eq_log_of_tendsto_rpow (spectrum.gelfand_formula N)

/-- The word sums `∑ i, (M ^ n *ᵥ 1) i` of a nonnegative matrix grow at least like the spectral
radius, by the Perron–Frobenius theorem. -/
theorem log_le_expGrowthInf_sum_pow_mulVec [Nonempty α] {M : Matrix α α ℝ}
    (hM : ∀ i j, 0 ≤ M i j) :
    ENNReal.log (spectralRadius ℂ (M.map (↑) : Matrix α α ℂ)) ≤
      expGrowthInf (fun n ↦ ENNReal.ofReal (∑ i, (M ^ n *ᵥ 1) i)) := by
  obtain ⟨r, hr, hρ, v, hv, hv0, hMv⟩ := Matrix.exists_mulVec_eq_smul_of_nonneg hM
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  have hvj : 0 < v j := (hv j).lt_of_ne' hj
  set D : ℝ := ∑ i, v i
  have hD : 0 < D := Finset.sum_pos' (fun i _ ↦ hv i) ⟨j, Finset.mem_univ j, hvj⟩
  have hpow (k : ℕ) : M ^ k *ᵥ v = r ^ k • v := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hMv, smul_smul,
        pow_succ', mul_comm]
  have hle (k : ℕ) : r ^ k * D ≤ D * ∑ i, (M ^ k *ᵥ 1) i := by
    have hvD : v ≤ D • (1 : α → ℝ) := fun i ↦ by
      simpa using Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hv i) (Finset.mem_univ i)
    have hmono : M ^ k *ᵥ v ≤ M ^ k *ᵥ (D • (1 : α → ℝ)) := fun i ↦
      Finset.sum_le_sum fun l _ ↦ mul_le_mul_of_nonneg_left (hvD l)
        (Matrix.pow_apply_nonneg hM k i l)
    rw [hpow, Matrix.mulVec_smul] at hmono
    calc r ^ k * D = ∑ i, (r ^ k • v) i := by simp [D, Finset.mul_sum]
      _ ≤ ∑ i, (D • (M ^ k *ᵥ 1)) i := Finset.sum_le_sum fun i _ ↦ hmono i
      _ = D * ∑ i, (M ^ k *ᵥ 1) i := by simp [Finset.mul_sum]
  rw [hρ, ← expGrowthInf_pow]
  refine expGrowthInf_monotone fun k ↦ ?_
  rw [← ENNReal.ofReal_pow hr]
  exact ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right (by linarith [hle k]) hD)

omit [DecidableEq α] in
/-- **Entropy of a subshift of finite type.** For a finite discrete alphabet and a `0`-`1`
transition matrix `M` without zero rows, the one-sided subshift of finite type `sftSet M` has
topological entropy `log (spectralRadius ℝ M)`. -/
theorem coverEntropy_shift_sftSet [UniformSpace α] [DiscreteUniformity α] [Nonempty α]
    {M : Matrix α α ℝ} (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) (hrow : ∀ i, ∃ j, M i j = 1) :
    coverEntropy (shift (1 : ℕ)) (sftSet M) = ENNReal.log (spectralRadius ℝ M) := by
  classical
  have hM : ∀ i j, 0 ≤ M i j := fun i j ↦ (h01 i j).elim (·.ge) fun h ↦ h ▸ zero_le_one
  have hmono : Monotone fun n ↦ (languageCount (sftSet M) n : ℝ≥0∞) :=
    fun _ _ h ↦ Nat.cast_le.2 (languageCount_mono _ h)
  have hL : (fun n ↦ (languageCount (sftSet M) (n + 1) : ℝ≥0∞)) =
      fun n ↦ ENNReal.ofReal (∑ i, (M ^ n *ᵥ 1) i) := by
    funext n
    rw [← languageCount_sftSet h01 hrow n, ENNReal.ofReal_natCast]
  rw [coverEntropy_shift_nat_eq_expGrowthSup, ← hmono.expGrowthSup_comp_add 1, hL,
    Matrix.spectralRadius_real_eq_of_nonneg hM]
  exact (expGrowthSup_sum_pow_mulVec_le hM).antisymm
    ((log_le_expGrowthInf_sum_pow_mulVec hM).trans expGrowthInf_le_expGrowthSup)

omit [DecidableEq α] in
/-- The `liminf` topological entropy of a subshift of finite type is also
`log (spectralRadius ℝ M)`. -/
theorem coverEntropyInf_shift_sftSet [UniformSpace α] [DiscreteUniformity α] [Nonempty α]
    {M : Matrix α α ℝ} (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) (hrow : ∀ i, ∃ j, M i j = 1) :
    coverEntropyInf (shift (1 : ℕ)) (sftSet M) = ENNReal.log (spectralRadius ℝ M) :=
  (coverEntropyInf_eq_coverEntropy _ (mapsTo_shift_sftSet M)).trans
    (coverEntropy_shift_sftSet h01 hrow)

end TauCeti
