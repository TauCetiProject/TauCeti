/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Scalar formal multilinear series

This file computes the formal composition of two scalar series in an arbitrary algebra. The
algebra need not be commutative: variables retain their original order inside every composition
block. It also identifies the iterated derivatives at zero of a convergent scalar series over a
complete nontrivially normed field.
-/

public section

open scoped BigOperators ENNReal

namespace FormalMultilinearSeries

variable {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E] [IsTopologicalRing E]

/-- Composing two scalar formal multilinear series gives the scalar series whose coefficients are
obtained by summing over compositions. This remains valid for noncommutative target algebras. -/
theorem ofScalars_comp_ofScalars (c d : ℕ → 𝕜) :
    (ofScalars E c).comp (ofScalars E d) =
      ofScalars E fun n ↦ ∑ p : Composition n, c p.length * ∏ i, d (p.blocksFun i) := by
  have prod_ofFn_smul {m : ℕ} (a : Fin m → 𝕜) (b : Fin m → E) :
      (List.ofFn fun i ↦ a i • b i).prod = (∏ i, a i) • (List.ofFn b).prod := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ, Fin.prod_univ_succ]
      simp only [List.prod_cons, ih]
      exact smul_mul_smul_comm _ _ _ _
  ext n v
  simp only [FormalMultilinearSeries.comp, ofScalars]
  rw [sum_apply, _root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hprod :
      (List.ofFn fun i : Fin p.length ↦ (ofScalars E d).applyComposition p v i).prod =
        (∏ i, d (p.blocksFun i)) • (List.ofFn v).prod := by
    simp only [applyComposition, ofScalars, _root_.smul_apply,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply]
    rw [prod_ofFn_smul]
    congr 1
    have hblocks :
        List.ofFn (fun i : Fin p.length ↦ (List.ofFn (v ∘ p.embedding i)).prod) =
          ((List.ofFn v).splitWrtComposition p).map List.prod := by
      refine List.ext_getElem (by simp) fun i hi₁ hi₂ ↦ ?_
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_splitWrtComposition]
      refine congrArg List.prod (List.ext_getElem ?_ fun j hj₁ hj₂ ↦ by simp; rfl)
      rw [List.length_ofFn, List.length_drop, List.length_take, List.length_ofFn,
        Nat.min_eq_left (p.sizeUpTo_le _), p.sizeUpTo_succ' ⟨i, by simpa using hi₁⟩,
        Nat.add_sub_cancel_left]
    rw [hblocks, ← List.prod_flatten, List.splitWrtComposition,
      List.flatten_splitWrtCompositionAux (by simp)]
  simp only [compAlongComposition_apply, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [hprod, smul_smul]

/-- Evaluating a term of the change-of-origin series of a scalar series at two constant vectors
produces the corresponding binomial coefficient. -/
theorem changeOriginSeries_ofScalars_apply {𝕂 R : Type*} [NontriviallyNormedField 𝕂]
    [NormedCommRing R] [NormedAlgebra 𝕂 R] (c : ℕ → 𝕂) (x y : R) (n l : ℕ) :
    (((ofScalars R c).changeOriginSeries n l) (fun _ ↦ x)) (fun _ ↦ y) =
      Nat.choose (n + l) l • (c (n + l) • (x ^ l * y ^ n)) := by
  -- The change-of-origin API exposes this coefficient through its defining finite sum. After
  -- unfolding it, each summand places `x` at the `l` indices of its finset and `y` elsewhere.
  rw [changeOriginSeries]
  simp only [_root_.sum_apply]
  simp_rw [changeOriginSeriesTerm_apply]
  have hx (s : {s : Finset (Fin (n + l)) // s.card = l}) :
      ofScalars R c (n + l) (s.val.piecewise (fun _ ↦ x) (fun _ ↦ y)) =
        c (n + l) • (x ^ l * y ^ n) := by
    simp only [ofScalars, _root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      List.prod_ofFn, Finset.prod_piecewise, Finset.univ_inter, Finset.prod_const,
      Finset.card_univ_sdiff, Fintype.card_fin, s.property, Nat.add_sub_cancel]
  simp_rw [hx]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin]

/-- The iterated derivatives at zero of the sum of a scalar formal multilinear series over a
complete nontrivially normed field recover its coefficients, up to the factorial normalization. -/
theorem iteratedDeriv_ofScalarsSum_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (c : ℕ → 𝕜) (hc : 0 < (ofScalars 𝕜 c).radius) (n : ℕ) :
    iteratedDeriv n (ofScalarsSum (E := 𝕜) c) 0 = n.factorial * c n := by
  have hseries := (ofScalars 𝕜 c).hasFPowerSeriesOnBall hc
  have hfac := hseries.factorial_smul (1 : 𝕜)
  simp only [apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    one_pow, one_mul, smul_eq_mul, coeff_ofScalars] at hfac
  have h := hfac n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h
  simpa [ofScalarsSum, nsmul_eq_mul, mul_comm] using h.symm

/-- Inside its ball of convergence, the iterated derivatives of a scalar power series are
given by the termwise differentiated series. -/
theorem _root_.HasFPowerSeriesOnBall.iteratedDeriv_eq_tsum_descFactorial_mul_pow
    {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂]
    {f : 𝕂 → 𝕂} {c : ℕ → 𝕂} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕂 c) 0 r) {y : 𝕂} (hy : ‖y‖ₑ < r) (n : ℕ) :
    iteratedDeriv n f y = ∑' k : ℕ, (k.descFactorial n : 𝕂) * c k * y ^ (k - n) := by
  let p := ofScalars 𝕂 c
  have hp_y := hf.changeOrigin (y := y) hy
  have hderiv :
      (n.factorial : 𝕂) * (p.changeOrigin y n) (fun _ ↦ (1 : 𝕂)) =
        iteratedDeriv n f y := by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    simpa only [p, zero_add, nsmul_eq_mul, Nat.cast_ofNat] using
      hp_y.factorial_smul (1 : 𝕂) n
  have h_radius : ‖y‖ₑ < p.radius := hy.trans_le hf.r_le
  have hp_change := p.hasFPowerSeriesOnBall_changeOrigin n (hf.r_pos.trans_le hf.r_le)
  have hsum_map := hp_change.hasSum (y := y) (by
    rw [mem_eball_zero_iff]
    exact h_radius)
  have hsum_coeff :
      HasSum (fun l : ℕ ↦ ((p.changeOriginSeries n l) (fun _ ↦ y))
        (fun _ ↦ (1 : 𝕂))) ((p.changeOrigin y n) (fun _ ↦ (1 : 𝕂))) :=
    by simpa only [zero_add] using
      ContinuousMultilinearMap.hasSum_eval hsum_map (fun _ ↦ (1 : 𝕂))
  have hsum_choose :
      HasSum (fun l : ℕ ↦ (Nat.choose (n + l) l : 𝕂) * c (n + l) * y ^ l)
        ((p.changeOrigin y n) (fun _ ↦ (1 : 𝕂))) := by
    convert hsum_coeff using 1
    ext l
    simpa only [p, nsmul_eq_mul, smul_eq_mul, one_pow, mul_one, mul_assoc] using
      (changeOriginSeries_ofScalars_apply c y (1 : 𝕂) n l).symm
  have hsum_tail :
      HasSum (fun l : ℕ ↦ ((n + l).descFactorial n : 𝕂) * c (n + l) * y ^ l)
        ((n.factorial : 𝕂) * (p.changeOrigin y n) (fun _ ↦ (1 : 𝕂))) := by
    convert hsum_choose.mul_left (n.factorial : 𝕂) using 1
    ext l
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_symm_add]
    push_cast
    ring
  let g : ℕ → 𝕂 := fun k ↦ (k.descFactorial n : 𝕂) * c k * y ^ (k - n)
  have hsum_tail' :
      HasSum (fun l : ℕ ↦ g (l + n))
        ((n.factorial : 𝕂) * (p.changeOrigin y n) (fun _ ↦ (1 : 𝕂))) := by
    simpa only [g, add_comm, Nat.add_sub_cancel_left] using hsum_tail
  have hprefix : ∑ k ∈ Finset.range n, g k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [g, Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hk), Nat.cast_zero,
      zero_mul]
  have hsum_desc :
      HasSum g ((n.factorial : 𝕂) * (p.changeOrigin y n) (fun _ ↦ (1 : 𝕂))) := by
    have h := (hasSum_nat_add_iff n).mp hsum_tail'
    simpa only [hprefix, add_zero] using h
  rw [← hderiv]
  exact hsum_desc.tsum_eq.symm

end FormalMultilinearSeries
