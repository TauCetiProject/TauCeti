/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic

/-!
# Scalar formal multilinear series

This file computes the formal composition of two scalar series in an arbitrary algebra. The
algebra need not be commutative: variables retain their original order inside every composition
block. It also identifies the iterated derivatives at zero of a convergent complex scalar series.
-/

public section

open scoped BigOperators ENNReal

namespace FormalMultilinearSeries

variable {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E]
  [IsTopologicalRing E]

omit [TopologicalSpace E] [IsTopologicalRing E] in
private theorem prod_ofFn_smul {n : ℕ} (a : Fin n → 𝕜) (b : Fin n → E) :
    (List.ofFn fun i ↦ a i • b i).prod = (∏ i, a i) • (List.ofFn b).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Fin.prod_univ_succ]
    simp only [List.prod_cons, ih]
    exact smul_mul_smul_comm _ _ _ _

omit [Ring E] [TopologicalSpace E] [IsTopologicalRing E] in
private theorem ofFn_embedding_eq_block {n : ℕ} (p : Composition n) (v : Fin n → E)
    (i : Fin p.length) :
    List.ofFn (fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)) =
      ((List.ofFn v).splitWrtComposition p).get
        ⟨i, by simp⟩ := by
  let p' : Composition (List.ofFn v).length := p.cast (by simp)
  have hsplit : (List.ofFn v).splitWrtComposition p' =
      (List.ofFn v).splitWrtComposition p := by rfl
  let ip : Fin ((List.ofFn v).splitWrtComposition p').length :=
    ⟨i, by
      simpa only [List.length_splitWrtComposition, p', Composition.cast] using i.isLt⟩
  have hblock := List.get_of_eq hsplit ip
  have hm := @List.getElem_of_eq _ _ _
      (List.map_length_splitWrtComposition (List.ofFn v) p') i.val (by
        simpa only [List.length_map, List.length_splitWrtComposition, p',
          Composition.cast] using i.isLt)
  have hlen :
      (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).length =
        (((List.ofFn v).splitWrtComposition p').get ip).length := by
    calc
      (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).length =
          p.blocksFun i := by simp
      _ = (((List.ofFn v).splitWrtComposition p').get ip).length := by
        simpa [p', Composition.blocksFun, ip] using hm.symm
  apply List.ext_getElem
  · calc
      _ = (((List.ofFn v).splitWrtComposition p').get ip).length := hlen
      _ = _ := congrArg List.length hblock
  · intro j hj₁ hj₂
    have hvalue := @List.getElem_of_eq _ _ _ hblock j (hlen ▸ hj₁)
    rw [List.getElem_ofFn]
    rw [← hvalue]
    simp only [List.get_eq_getElem]
    have hslice := List.getElem_splitWrtComposition (List.ofFn v) p' ip.val ip.isLt
    have hsliceValue := @List.getElem_of_eq _ _ _ hslice j (hlen ▸ hj₁)
    rw [hsliceValue]
    simp only [List.getElem_drop, List.getElem_take, List.getElem_ofFn]
    apply congrArg v
    apply Fin.ext
    rfl

omit [TopologicalSpace E] [IsTopologicalRing E] in
private theorem prod_blocks {n : ℕ} (p : Composition n) (v : Fin n → E) :
    (List.ofFn fun i : Fin p.length ↦
        (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).prod).prod =
      (List.ofFn v).prod := by
  have h :
      List.ofFn (fun i : Fin p.length ↦
          (List.ofFn fun j : Fin (p.blocksFun i) ↦ v (p.embedding i j)).prod) =
        ((List.ofFn v).splitWrtComposition p).map List.prod := by
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn, List.getElem_map]
      exact congrArg List.prod (ofFn_embedding_eq_block p v ⟨i, by simpa using hi₁⟩)
  rw [h, ← List.prod_flatten]
  let p' : Composition (List.ofFn v).length := p.cast (by simp)
  have hsplit : (List.ofFn v).splitWrtComposition p' =
      (List.ofFn v).splitWrtComposition p := by rfl
  rw [← hsplit, List.flatten_splitWrtComposition]

private theorem prod_applyComposition_ofScalars {n : ℕ} (d : ℕ → 𝕜) (p : Composition n)
    (v : Fin n → E) :
    (List.ofFn fun i : Fin p.length ↦
        (ofScalars E d).applyComposition p v i).prod =
      (∏ i, d (p.blocksFun i)) • (List.ofFn v).prod := by
  simp only [applyComposition, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [prod_ofFn_smul]
  congr 1
  exact prod_blocks p v

/-- Composing two scalar formal multilinear series gives the scalar series whose coefficients are
obtained by summing over compositions. This remains valid for noncommutative target algebras. -/
theorem ofScalars_comp_ofScalars (c d : ℕ → 𝕜) :
    (ofScalars E c).comp (ofScalars E d) =
      ofScalars E fun n ↦ ∑ p : Composition n, c p.length * ∏ i, d (p.blocksFun i) := by
  ext n v
  simp only [FormalMultilinearSeries.comp, ofScalars]
  rw [sum_apply, _root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p _
  simp only [compAlongComposition_apply, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  rw [prod_applyComposition_ofScalars]
  simp only [smul_smul]

/-- Evaluating a term of the change-of-origin series of a scalar series at a constant vector
produces the corresponding binomial coefficient. -/
theorem changeOriginSeries_ofScalars_apply {𝕂 R : Type*} [NontriviallyNormedField 𝕂]
    [NormedRing R] [NormedAlgebra 𝕂 R] (c : ℕ → 𝕂) (x : R) (n l : ℕ) :
    (((ofScalars R c).changeOriginSeries n l) (fun _ ↦ x)) (fun _ ↦ x) =
      Nat.choose (n + l) l • (c (n + l) • x ^ (n + l)) := by
  -- The change-of-origin API exposes this coefficient through its defining finite sum. After
  -- unfolding it, every piecewise constant input is the same constant vector.
  rw [changeOriginSeries]
  simp only [_root_.sum_apply]
  simp_rw [changeOriginSeriesTerm_apply]
  have hx (s : {s : Finset (Fin (n + l)) // s.card = l}) :
      s.val.piecewise (fun _ ↦ x) (fun _ ↦ x) = fun _ ↦ x := by
    funext i
    simp only [Finset.piecewise_same]
  simp_rw [hx, ofScalars_apply_eq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin]

/-- The iterated derivatives at zero of the sum of a complex scalar formal multilinear series
recover its coefficients, up to the factorial normalization. -/
theorem iteratedDeriv_ofScalarsSum_zero (c : ℕ → ℂ)
    (hc : 0 < (ofScalars ℂ c).radius) (n : ℕ) :
    iteratedDeriv n (ofScalarsSum (E := ℂ) c) 0 = n.factorial * c n := by
  have hseries :=
    (ofScalars ℂ c).hasFPowerSeriesOnBall hc
  have hfac := hseries.factorial_smul (1 : ℂ)
  simp only [apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    one_pow, one_mul, smul_eq_mul, coeff_ofScalars] at hfac
  have h := hfac n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h
  simpa [ofScalarsSum, mul_comm] using h.symm

/-- Inside its ball of convergence, the iterated derivatives of a real scalar power series are
the sums of its falling-factorial-weighted coefficients. -/
theorem HasFPowerSeriesOnBall.iteratedDeriv_one_eq_tsum_descFactorial_mul
    {f : ℝ → ℝ} {c : ℕ → ℝ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars ℝ c) 0 r) (h_one : (1 : ℝ≥0∞) < r) (n : ℕ) :
    iteratedDeriv n f 1 = ∑' k : ℕ, (k.descFactorial n : ℝ) * c k := by
  let p := ofScalars ℝ c
  have hp_one := hf.changeOrigin (y := (1 : ℝ)) (by simpa using h_one)
  have hderiv :
      (n.factorial : ℝ) * (p.changeOrigin 1 n) (fun _ ↦ (1 : ℝ)) =
        iteratedDeriv n f 1 := by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    simpa only [p, zero_add, nsmul_eq_mul, Nat.cast_ofNat] using
      hp_one.factorial_smul (1 : ℝ) n
  have h_radius : (1 : ℝ≥0∞) < p.radius := h_one.trans_le hf.r_le
  have hp_change := p.hasFPowerSeriesOnBall_changeOrigin n (hf.r_pos.trans_le hf.r_le)
  have hsum_map := hp_change.hasSum (y := (1 : ℝ)) (by
    rw [mem_eball_zero_iff]
    simpa using h_radius)
  have hsum_coeff :
      HasSum (fun l : ℕ ↦ ((p.changeOriginSeries n l) (fun _ ↦ (1 : ℝ)))
        (fun _ ↦ (1 : ℝ))) ((p.changeOrigin 1 n) (fun _ ↦ (1 : ℝ))) :=
    by simpa only [zero_add] using
      ContinuousMultilinearMap.hasSum_eval hsum_map (fun _ ↦ (1 : ℝ))
  have hsum_choose :
      HasSum (fun l : ℕ ↦ (Nat.choose (n + l) l : ℝ) * c (n + l))
        ((p.changeOrigin 1 n) (fun _ ↦ (1 : ℝ))) := by
    convert hsum_coeff using 1
    ext l
    simpa only [p, nsmul_eq_mul, smul_eq_mul, one_pow, mul_one] using
      (changeOriginSeries_ofScalars_apply c (1 : ℝ) n l).symm
  have hsum_tail :
      HasSum (fun l : ℕ ↦ ((n + l).descFactorial n : ℝ) * c (n + l))
        ((n.factorial : ℝ) * (p.changeOrigin 1 n) (fun _ ↦ (1 : ℝ))) := by
    convert hsum_choose.mul_left (n.factorial : ℝ) using 1
    ext l
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_symm_add]
    push_cast
    ring
  let g : ℕ → ℝ := fun k ↦ (k.descFactorial n : ℝ) * c k
  have hsum_tail' :
      HasSum (fun l : ℕ ↦ g (l + n))
        ((n.factorial : ℝ) * (p.changeOrigin 1 n) (fun _ ↦ (1 : ℝ))) := by
    simpa only [g, add_comm] using hsum_tail
  have hprefix : ∑ k ∈ Finset.range n, g k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [g, Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hk), Nat.cast_zero,
      zero_mul]
  have hsum_desc :
      HasSum g ((n.factorial : ℝ) * (p.changeOrigin 1 n) (fun _ ↦ (1 : ℝ))) := by
    have h := (hasSum_nat_add_iff n).mp hsum_tail'
    simpa only [hprefix, add_zero] using h
  rw [← hderiv]
  exact hsum_desc.tsum_eq.symm

end FormalMultilinearSeries
