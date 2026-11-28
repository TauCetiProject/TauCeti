/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Factor
import TauCeti.Topology.Algebra.InfiniteSum.Real
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# Paired quadratic canonical products

When zeros of an even entire function occur in opposite pairs `±i γ_n` (`γ_n > 0`), the genus-one
Weierstrass factors multiply to paired quadratic factors `1 + z ^ 2 / γ_n ^ 2`. Under totalized
division (`z ^ 2 / 0 = 0`), this expression automatically evaluates to `1` at padded `γ_n = 0`
entries, avoiding conditional branching in convergence and coefficient proofs.

## Main results

* `TauCeti.hasProdUniformlyOn_one_add_div_sq`, `TauCeti.hasProd_one_add_div_sq`, and
  `TauCeti.tendstoUniformlyOn_mul_pow_one_add_div_sq`: compact uniform and pointwise convergence
  from inverse-square summability `∑' n, (γ n)⁻¹ ^ 2 < ∞`.
* `TauCeti.one_le_tprod_one_add_div_sq`: on `ℝ`, the paired product is real and at least `1` in
  `ComplexOrder`.
* `TauCeti.im_eq_zero_and_re_pos_of_eq_mul_pow_tprod_one_add_div_sq`: real positivity at a single
  positive real point forces the leading constant of a paired quadratic product to be real and
  strictly positive.
* `TauCeti.exists_nat_seq_tprod_one_add_div_sq`: flattening an arbitrary inverse-square-summable
  family with multiplicities into a `0`-padded `ℕ`-indexed sequence.
-/

public section

open Complex Filter Metric Topology
open scoped BigOperators

namespace TauCeti

/-- Square-summability of `(γ n)⁻¹` yields uniform convergence on every compact set `K ⊆ ℂ` of the
paired quadratic infinite product. -/
theorem hasProdUniformlyOn_one_add_div_sq {γ : ℕ → ℝ}
    (hsum : Summable (fun n : ℕ ↦ (γ n)⁻¹ ^ 2)) {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun (n : ℕ) (z : ℂ) ↦ 1 + z ^ 2 / (γ n : ℂ) ^ 2)
      (fun z : ℂ ↦ ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2)) K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  set B : ℝ := max M 0
  have hu : Summable (fun n : ℕ ↦ B ^ 2 * (γ n)⁻¹ ^ 2) := hsum.mul_left (B ^ 2)
  have hbound : ∀ᶠ n : ℕ in cofinite, ∀ z ∈ K,
      ‖((((γ n)⁻¹ ^ 2 : ℝ) : ℂ)) * z ^ 2‖ ≤ B ^ 2 * (γ n)⁻¹ ^ 2 := by
    refine Eventually.of_forall fun n z hz ↦ ?_
    have hzB : ‖z‖ ≤ B := (hM z hz).trans (le_max_left M 0)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    calc (γ n)⁻¹ ^ 2 * ‖z‖ ^ 2 ≤ (γ n)⁻¹ ^ 2 * B ^ 2 := by gcongr
      _ = B ^ 2 * (γ n)⁻¹ ^ 2 := mul_comm _ _
  have hcts : ∀ n : ℕ, ContinuousOn (fun z : ℂ ↦ ((((γ n)⁻¹ ^ 2 : ℝ) : ℂ)) * z ^ 2) K :=
    fun _ ↦ by fun_prop
  have hp := Summable.hasProdUniformlyOn_one_add hK hu hbound hcts
  have hcongr : ∀ n z, 1 + z ^ 2 / (γ n : ℂ) ^ 2 =
      1 + ((((γ n)⁻¹ ^ 2 : ℝ) : ℂ)) * z ^ 2 := fun n ↦ one_add_div_sq_eq_one_add_inv_sq_mul (γ n)
  simpa only [← hcongr] using hp

/-- Pointwise convergence of the paired quadratic infinite product at any `z : ℂ`. -/
theorem hasProd_one_add_div_sq {γ : ℕ → ℝ}
    (hsum : Summable (fun n : ℕ ↦ (γ n)⁻¹ ^ 2)) (z : ℂ) :
    HasProd (fun n : ℕ ↦ 1 + z ^ 2 / (γ n : ℂ) ^ 2)
      (∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2)) :=
  (hasProdUniformlyOn_one_add_div_sq hsum (isCompact_singleton (x := z))).hasProd
    (Set.mem_singleton z)

section
open scoped ComplexOrder

/-- At any real point `x : ℝ`, the paired infinite product satisfies `1 ≤ ∏' n, ...` in
`ComplexOrder` (in particular, its imaginary part is `0` and its real part is at least `1`). -/
theorem one_le_tprod_one_add_div_sq {γ : ℕ → ℝ}
    (hsum : Summable (fun n : ℕ ↦ (γ n)⁻¹ ^ 2)) (x : ℝ) :
    (1 : ℂ) ≤ ∏' n : ℕ, (1 + (x : ℂ) ^ 2 / (γ n : ℂ) ^ 2) := by
  have hreal : (fun n : ℕ ↦ 1 + (x : ℂ) ^ 2 / (γ n : ℂ) ^ 2) =
      fun n : ℕ ↦ Complex.ofRealHom (1 + (γ n)⁻¹ ^ 2 * x ^ 2) := by
    ext n
    rw [one_add_div_sq_eq_one_add_inv_sq_mul]
    simp [Complex.ofRealHom_eq_coe, mul_comm]
  rw [hreal, ← Complex.isometry_ofReal.isClosedEmbedding.map_tprod _ (g := Complex.ofRealHom)]
  have hhp : HasProd (fun n : ℕ ↦ 1 + (γ n)⁻¹ ^ 2 * x ^ 2)
      (∏' n : ℕ, (1 + (γ n)⁻¹ ^ 2 * x ^ 2)) :=
    (Real.multipliable_one_add_of_summable (hsum.mul_right (x ^ 2))).hasProd
  have hle : 1 ≤ ∏' n : ℕ, (1 + (γ n)⁻¹ ^ 2 * x ^ 2) := by
    simpa using prod_le_hasProd_of_nonneg (s := ∅) (by simp)
      (fun n _ ↦ le_add_of_nonneg_right (by positivity)) hhp
  simpa only [Complex.ofRealHom_eq_coe, Complex.ofReal_one] using Complex.real_le_real.mpr hle

end

/-- Evaluating `f z = a * z ^ m * ∏' n, (1 + z ^ 2 / (γ n) ^ 2)` at a single positive real point
`x₀ > 0` where `f x₀` is real and strictly positive forces the leading constant `a` to be real
and strictly positive. -/
theorem im_eq_zero_and_re_pos_of_eq_mul_pow_tprod_one_add_div_sq {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    {γ : ℕ → ℝ} (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = a * z ^ m * ∏' n, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    {x₀ : ℝ} (hx₀ : 0 < x₀) (him : (f (x₀ : ℂ)).im = 0) (hre : 0 < (f (x₀ : ℂ)).re) :
    a.im = 0 ∧ 0 < a.re := by
  open scoped ComplexOrder in
  have hP_le : (1 : ℂ) ≤ ∏' n : ℕ, (1 + (x₀ : ℂ) ^ 2 / (γ n : ℂ) ^ 2) :=
    one_le_tprod_one_add_div_sq hsum x₀
  set P₀ : ℂ := ∏' n : ℕ, (1 + (x₀ : ℂ) ^ 2 / (γ n : ℂ) ^ 2) with hP₀_def
  have hK_pos : 0 < x₀ ^ m * P₀.re :=
    mul_pos (pow_pos hx₀ m) (zero_lt_one.trans_le (Complex.le_def.mp hP_le).1)
  have hP_coe : P₀ = (P₀.re : ℂ) := by
    open scoped ComplexOrder in
    exact Complex.eq_re_of_ofReal_le (r := 1) (by simpa only [Complex.ofReal_one] using hP_le)
  have hfx_eval : f (x₀ : ℂ) = a * (((x₀ ^ m * P₀.re : ℝ) : ℂ)) := by
    conv_lhs => rw [hf_eq (x₀ : ℂ), ← hP₀_def, hP_coe]
    push_cast
    ring
  have ha_im : a.im = 0 := by
    have h := congrArg Complex.im hfx_eval
    rw [him, im_mul_ofReal] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hK_pos.ne'
  have ha_re : 0 < a.re := by
    have h := congrArg Complex.re hfx_eval
    rw [re_mul_ofReal] at h
    exact pos_of_mul_pos_left (h ▸ hre) hK_pos.le
  exact ⟨ha_im, ha_re⟩

/-- Any product `∏' i : α, (1 + z ^ 2 / (y i) ^ 2) ^ (m i)` with `0 < y i` and
`∑' i, m i * (y i)⁻¹ ^ 2 < ∞` can be flattened into an `ℕ`-indexed paired product padded by `0`. -/
theorem exists_nat_seq_tprod_one_add_div_sq {α : Type*} {y : α → ℝ} {m : α → ℕ}
    (hy : ∀ i, 0 < y i) (hsum : Summable (fun i ↦ (m i : ℝ) * (y i)⁻¹ ^ 2)) :
    ∃ γ : ℕ → ℝ, (∀ n, 0 ≤ γ n) ∧ Summable (fun n ↦ (γ n)⁻¹ ^ 2) ∧
      ∀ z : ℂ, (∏' i : α, (1 + z ^ 2 / (y i : ℂ) ^ 2) ^ m i) =
        ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2) := by
  classical
  let ι := Σ i : α, Fin (m i)
  have hι_sum : Summable (fun p : ι ↦ (y p.1)⁻¹ ^ 2) :=
    (summable_sigma_fin_iff (fun i ↦ sq_nonneg (y i)⁻¹) m).mpr hsum
  have hcount_ι : Countable ι := by
    rw [← Set.countable_univ_iff]
    exact hι_sum.countable_support.mono fun p _ ↦ pow_ne_zero 2 (inv_ne_zero (hy p.1).ne')
  obtain ⟨emb, hemb⟩ := Countable.exists_injective_nat ι
  let γ : ℕ → ℝ := Function.extend emb (fun p : ι ↦ y p.1) 0
  have hγ_nonneg (n : ℕ) : 0 ≤ γ n := by
    dsimp only [γ]
    rw [Function.extend_def]
    split_ifs with hn
    · exact (hy hn.choose.1).le
    · exact le_rfl
  have hγ_ext {β : Type} (φ : ℝ → β) (b₀ : β) (h0 : φ 0 = b₀) (n : ℕ) :
      φ (γ n) = Function.extend emb (fun p : ι ↦ φ (y p.1)) (fun _ ↦ b₀) n := by
    rw [Function.apply_extend φ, Function.comp_def, Function.comp_def]
    simp only [Pi.zero_apply, h0]
  have hγ_inv_eq : (fun n : ℕ ↦ (γ n)⁻¹ ^ 2) =
      Function.extend emb (fun p : ι ↦ (y p.1)⁻¹ ^ 2) 0 :=
    funext fun n ↦ by
      simpa only [← Pi.zero_def] using hγ_ext (fun r : ℝ ↦ r⁻¹ ^ 2) 0 (by norm_num) n
  have hγ_sum : Summable (fun n : ℕ ↦ (γ n)⁻¹ ^ 2) := by
    rw [hγ_inv_eq]
    exact (summable_extend_zero hemb).mpr hι_sum
  refine ⟨γ, hγ_nonneg, hγ_sum, fun z ↦ ?_⟩
  have hfactor_ext :
      (fun n : ℕ ↦ (1 : ℂ) + z ^ 2 / (γ n : ℂ) ^ 2) =
        Function.extend emb (fun p : ι ↦ (1 : ℂ) + z ^ 2 / (y p.1 : ℂ) ^ 2) 1 :=
    funext fun n ↦ by
      simpa only [← Pi.one_def] using
        hγ_ext (fun r : ℝ ↦ (1 : ℂ) + z ^ 2 / (r : ℂ) ^ 2) 1 (by simp) n
  have hmult_nat : Multipliable (fun n : ℕ ↦ (1 : ℂ) + z ^ 2 / (γ n : ℂ) ^ 2) :=
    (hasProd_one_add_div_sq hγ_sum z).multipliable
  rw [hfactor_ext] at hmult_nat
  have hmult_ι : Multipliable (fun p : ι ↦ (1 : ℂ) + z ^ 2 / (y p.1 : ℂ) ^ 2) :=
    (multipliable_extend_one hemb).mp hmult_nat
  rw [hfactor_ext, tprod_extend_one hemb,
    Multipliable.tprod_sigma' (fun _ ↦ Multipliable.of_finite) hmult_ι]
  simp only [tprod_fintype, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Multiplying the compactly uniformly convergent paired partial products by `a * z ^ m` preserves
uniform convergence on any compact set `K ⊆ ℂ`. -/
theorem tendstoUniformlyOn_mul_pow_one_add_div_sq (a : ℂ) (m : ℕ) {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2)) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun (s : Finset ℕ) (z : ℂ) ↦ a * z ^ m * ∏ n ∈ s, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
      (fun z : ℂ ↦ a * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
      atTop K := by
  have hp := (hasProdUniformlyOn_one_add_div_sq hsum hK).tendstoUniformlyOn
  have hp_cts : ContinuousOn
      (fun z : ℂ ↦ ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2)) K :=
    hp.continuousOn ((Eventually.of_forall fun s : Finset ℕ ↦
      continuousOn_finsetProd (s := s) fun n _ ↦ by
        simp_rw [one_add_div_sq_eq_one_add_inv_sq_mul]; fun_prop).frequently)
  have hconst : TendstoLocallyUniformlyOn
      (fun (_ : Finset ℕ) (z : ℂ) ↦ a * z ^ m)
      (fun z : ℂ ↦ a * z ^ m) atTop K :=
    (tendstoUniformlyOn_const (fun z : ℂ ↦ a * z ^ m) atTop K).tendstoLocallyUniformlyOn
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hconst.fun_mul₀ hp.tendstoLocallyUniformlyOn (by fun_prop) hp_cts)

end TauCeti
