/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.FrequencyCutoff
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Homogeneous symbols

A homogeneous symbol of degree `m` on a real normed space `E` is a map
`a : E × E → (V →L[ℂ] W)`, of a position `x` and a frequency `ξ`, which is smooth away from the
zero frequency, positively homogeneous of degree `m` in the frequency,
`a(x, t ξ) = t ^ m a(x, ξ)` for `t > 0`, and which takes the value `0` at `ξ = 0`. The degree is
an arbitrary real number. The value at the zero frequency is only a convention: a homogeneous
term need not be continuous there. The terms `a_{m - j}` of a classical expansion of a symbol and
its principal symbol are homogeneous symbols.

Homogeneous symbols of a fixed degree form a complex vector space, and pointwise composition of
coefficients adds the degrees (`TauCeti.HomogeneousSymbol.comp`). On an inner product space the
powers `‖ξ‖ ^ m` of the frequency norm are homogeneous symbols of every degree
(`TauCeti.HomogeneousSymbol.normRpow`).

Differentiating the homogeneity relation shows that the derivatives of `a` in `j` position
directions and `l` frequency directions are homogeneous of degree `m - l`. Since `a` is continuous
on the compact sets `K × {‖ξ‖ = 1}`, this gives the estimate `≤ C ‖ξ‖ ^ (m - l)` on `K × E`
(`TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_le`). Multiplying `a` by a frequency
cutoff `χ` gives a smooth function `χ(ξ) a(x, ξ)` on all of `E × E` which satisfies the symbol
estimates of order `m`, with the weight `⟨ξ⟩ ^ (m - l) = (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2)`
(`TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_frequencyCutoff_smul_le`); changing the
cutoff changes it by a smoothing term, whose derivatives decay faster than every power of `⟨ξ⟩`
(`TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_sub_frequencyCutoff_smul_le`).

Derivatives are full Fréchet derivatives on `E × E`; a derivative in `j` position directions
`u` and `l` frequency directions `w` is the iterated derivative evaluated on
`Fin.append (fun i ↦ (u i, 0)) (fun i ↦ (0, w i))`.

## Main declarations

* `TauCeti.HomogeneousSymbol E V W m`: homogeneous symbols of degree `m`.
* `TauCeti.HomogeneousSymbol.comp`: composition of coefficients, adding the degrees.
* `TauCeti.HomogeneousSymbol.normRpow`: the symbol `‖ξ‖ ^ m` times the identity.
* `TauCeti.HomogeneousSymbol.iteratedFDeriv_coefficient_smul_frequency`: homogeneity of the
  derivatives.
* `TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_le`: the estimate
  `‖∂_x^j ∂_ξ^l a(x, ξ)‖ ≤ C ‖ξ‖ ^ (m - l)` for `x` in a compact set.
* `TauCeti.HomogeneousSymbol.contDiff_frequencyCutoff_smul` and
  `TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_frequencyCutoff_smul_le`: the cut-off
  term is smooth and satisfies the symbol estimates of order `m`.

## References

* M. E. Taylor, *Pseudodifferential Operators*, Lecture I, (1.15)–(1.17).
* R. B. Melrose, *Introduction to Microlocal Analysis*, Chapter 2.
-/

public section

noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]
  {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

section NormedSpace

variable [NormedSpace ℝ E]

variable (E V W) in
/-- A homogeneous symbol of degree `m`: a map `a(x, ξ)` of a position `x` and a frequency `ξ`
which is smooth on `ξ ≠ 0`, satisfies `a(x, t ξ) = t ^ m a(x, ξ)` for `t > 0`, and vanishes at
`ξ = 0` by convention. -/
@[ext]
structure HomogeneousSymbol (m : ℝ) where
  /-- The coefficient `a(x, ξ)` at the position `x` and the frequency `ξ`. -/
  coefficient : E × E → V →L[ℂ] W
  /-- The value at the zero frequency is `0` by convention. -/
  coefficient_zero_frequency : ∀ x, coefficient (x, 0) = 0
  /-- The coefficient is smooth away from the zero frequency. -/
  contDiffOn_coefficient : ContDiffOn ℝ ∞ coefficient {p | p.2 ≠ 0}
  /-- Positive homogeneity of degree `m` in the frequency. -/
  coefficient_smul_frequency_of_ne_zero :
    ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → coefficient (x, t • ξ) = t ^ m • coefficient (x, ξ)

namespace HomogeneousSymbol

variable {m m' : ℝ}

theorem coefficient_injective :
    Function.Injective (coefficient : HomogeneousSymbol E V W m → E × E → V →L[ℂ] W) :=
  fun _ _ h => HomogeneousSymbol.ext h

attribute [simp] coefficient_zero_frequency

/-- Positive homogeneity holds at every frequency, the zero frequency included. -/
theorem coefficient_smul_frequency (a : HomogeneousSymbol E V W m) (x ξ : E) {t : ℝ}
    (ht : 0 < t) : a.coefficient (x, t • ξ) = t ^ m • a.coefficient (x, ξ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · exact a.coefficient_smul_frequency_of_ne_zero x ξ hξ t ht

omit [NormedSpace ℝ E] in
private theorem isOpen_setOf_snd_ne_zero : IsOpen {p : E × E | p.2 ≠ 0} :=
  isOpen_ne_fun continuous_snd continuous_const

theorem contDiffAt_coefficient (a : HomogeneousSymbol E V W m) {p : E × E} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ a.coefficient p :=
  a.contDiffOn_coefficient.contDiffAt (isOpen_setOf_snd_ne_zero.mem_nhds hp)

theorem continuousOn_iteratedFDeriv_coefficient (a : HomogeneousSymbol E V W m) (k : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ k a.coefficient) {p | p.2 ≠ 0} :=
  (a.contDiffOn_coefficient.continuousOn_iteratedFDerivWithin (mod_cast le_top)
    isOpen_setOf_snd_ne_zero.uniqueDiffOn).congr
      fun _ hp => (iteratedFDerivWithin_of_isOpen k isOpen_setOf_snd_ne_zero hp).symm

/-! ### The vector space of homogeneous symbols of a fixed degree -/

section Module

instance : Zero (HomogeneousSymbol E V W m) where
  zero :=
    { coefficient := 0
      coefficient_zero_frequency := fun _ => rfl
      contDiffOn_coefficient := contDiffOn_const
      coefficient_smul_frequency_of_ne_zero := fun _ _ _ _ _ => by simp }

instance : Add (HomogeneousSymbol E V W m) where
  add a b :=
    { coefficient := a.coefficient + b.coefficient
      coefficient_zero_frequency := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_coefficient.add b.contDiffOn_coefficient
      coefficient_smul_frequency_of_ne_zero := fun x ξ _ t ht => by
        simp [a.coefficient_smul_frequency x ξ ht, b.coefficient_smul_frequency x ξ ht] }

instance : SMul ℂ (HomogeneousSymbol E V W m) where
  smul c a :=
    { coefficient := c • a.coefficient
      coefficient_zero_frequency := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_coefficient.const_smul c
      coefficient_smul_frequency_of_ne_zero := fun x ξ _ t ht => by
        simp [a.coefficient_smul_frequency x ξ ht, smul_comm c] }

instance : Neg (HomogeneousSymbol E V W m) where
  neg a :=
    { coefficient := -a.coefficient
      coefficient_zero_frequency := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_coefficient.neg
      coefficient_smul_frequency_of_ne_zero := fun x ξ _ t ht => by
        simp [a.coefficient_smul_frequency x ξ ht] }

instance : Sub (HomogeneousSymbol E V W m) where
  sub a b :=
    { coefficient := a.coefficient - b.coefficient
      coefficient_zero_frequency := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_coefficient.sub b.contDiffOn_coefficient
      coefficient_smul_frequency_of_ne_zero := fun x ξ _ t ht => by
        simp [a.coefficient_smul_frequency x ξ ht, b.coefficient_smul_frequency x ξ ht,
          smul_sub] }

instance : SMul ℕ (HomogeneousSymbol E V W m) where
  smul k a :=
    { coefficient := k • a.coefficient
      coefficient_zero_frequency := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_coefficient.const_smul k
      coefficient_smul_frequency_of_ne_zero := fun x ξ _ t ht => by
        simp [a.coefficient_smul_frequency x ξ ht, smul_comm k] }

instance : SMul ℤ (HomogeneousSymbol E V W m) where
  smul k a :=
    { coefficient := k • a.coefficient
      coefficient_zero_frequency := fun x => by simp
      contDiffOn_coefficient := a.contDiffOn_coefficient.const_smul k
      coefficient_smul_frequency_of_ne_zero := fun x ξ _ t ht => by
        simp [a.coefficient_smul_frequency x ξ ht, smul_comm k] }

@[simp]
theorem coefficient_zero : (0 : HomogeneousSymbol E V W m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_add (a b : HomogeneousSymbol E V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : HomogeneousSymbol E V W m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : HomogeneousSymbol E V W m) : (-a).coefficient = -a.coefficient :=
  (rfl)

@[simp]
theorem coefficient_sub (a b : HomogeneousSymbol E V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient := (rfl)

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : HomogeneousSymbol E V W m) :
    (k • a).coefficient = k • a.coefficient := (rfl)

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : HomogeneousSymbol E V W m) :
    (k • a).coefficient = k • a.coefficient := (rfl)

instance : AddCommGroup (HomogeneousSymbol E V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k => coefficient_nsmul k a) (fun a k => coefficient_zsmul k a)

instance : Module ℂ (HomogeneousSymbol E V W m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩
    coefficient_smul

end Module

/-! ### Composition of coefficients -/

section Comp

/-- Pointwise composition of coefficients: the composition `b(x, ξ) ∘ a(x, ξ)` of homogeneous
symbols of degrees `m` and `m'` is homogeneous of degree `m + m'`. -/
def comp (b : HomogeneousSymbol E V W m) (a : HomogeneousSymbol E U V m') :
    HomogeneousSymbol E U W (m + m') where
  coefficient p := (b.coefficient p).comp (a.coefficient p)
  coefficient_zero_frequency x := by simp
  contDiffOn_coefficient :=
    ((ContinuousLinearMap.compL ℂ U V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff
      |>.comp₂_contDiffOn b.contDiffOn_coefficient a.contDiffOn_coefficient
  coefficient_smul_frequency_of_ne_zero x ξ _ t ht := by
    rw [b.coefficient_smul_frequency x ξ ht, a.coefficient_smul_frequency x ξ ht,
      Real.rpow_add ht, mul_smul]
    ext v
    simp [smul_comm (t ^ m) (t ^ m')]

@[simp]
theorem coefficient_comp (b : HomogeneousSymbol E V W m) (a : HomogeneousSymbol E U V m')
    (p : E × E) : (b.comp a).coefficient p = (b.coefficient p).comp (a.coefficient p) := (rfl)

end Comp

/-! ### Estimates for the derivatives -/

section Derivatives

variable (a : HomogeneousSymbol E V W m)

/-- The derivatives of a homogeneous symbol are homogeneous: rescaling the frequency by `t > 0`,
together with the frequency components of the directions, multiplies the derivative by
`t ^ m`. -/
theorem iteratedFDeriv_coefficient_smul_frequency {x ξ : E} (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t)
    (k : ℕ) (v : Fin k → E × E) :
    iteratedFDeriv ℝ k a.coefficient (x, t • ξ) (fun i => ((v i).1, t • (v i).2)) =
      t ^ m • iteratedFDeriv ℝ k a.coefficient (x, ξ) v := by
  let S : E × E →L[ℝ] E × E := (ContinuousLinearMap.id ℝ E).prodMap (t • ContinuousLinearMap.id ℝ E)
  have hS : S ⁻¹' {p : E × E | p.2 ≠ 0} = {p | p.2 ≠ 0} := by
    ext p
    simp [S, ht.ne']
  have hcomp : a.coefficient ∘ S = t ^ m • a.coefficient := by
    ext1 p
    exact a.coefficient_smul_frequency p.1 p.2 ht
  have hξ' : (x, ξ) ∈ {p : E × E | p.2 ≠ 0} := hξ
  have key := S.iteratedFDerivWithin_comp_right a.contDiffOn_coefficient
    isOpen_setOf_snd_ne_zero.uniqueDiffOn (by rw [hS]; exact isOpen_setOf_snd_ne_zero.uniqueDiffOn)
    (x := (x, ξ)) (by simpa [S, ht.ne'] using hξ) (i := k) (mod_cast le_top)
  rw [hS, hcomp, iteratedFDerivWithin_of_isOpen k isOpen_setOf_snd_ne_zero hξ',
    iteratedFDerivWithin_of_isOpen k isOpen_setOf_snd_ne_zero (by simpa [S, ht.ne'] using hξ),
    iteratedFDeriv_const_smul_apply ((a.contDiffAt_coefficient hξ).of_le (mod_cast le_top))] at key
  have := congr($key v)
  simpa [S, Prod.map, Pi.smul_apply] using this.symm

/-- The derivative of a homogeneous symbol of degree `m` in `j` position directions and `l`
frequency directions is homogeneous of degree `m - l` in the frequency. -/
theorem iteratedFDeriv_coefficient_smul_frequency_append {x ξ : E} (hξ : ξ ≠ 0) {t : ℝ}
    (ht : 0 < t) {j l : ℕ} (u : Fin j → E) (w : Fin l → E) :
    iteratedFDeriv ℝ (j + l) a.coefficient (x, t • ξ)
        (Fin.append (fun i => (u i, 0)) (fun i => (0, w i))) =
      t ^ (m - l) •
        iteratedFDeriv ℝ (j + l) a.coefficient (x, ξ)
          (Fin.append (fun i => (u i, 0)) (fun i => (0, w i))) := by
  set D := iteratedFDeriv ℝ (j + l) a.coefficient (x, t • ξ)
  set v : Fin (j + l) → E × E := Fin.append (fun i => (u i, 0)) (fun i => (0, w i))
  have hscale : (fun i => ((v i).1, t • (v i).2)) =
      fun i => (Fin.append (fun _ => (1 : ℝ)) (fun _ => t) i) • v i := by
    ext1 i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [v]
  have h := a.iteratedFDeriv_coefficient_smul_frequency (x := x) hξ ht (j + l) v
  rw [hscale, D.map_smul_univ, Fin.prod_univ_add] at h
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, one_mul] at h
  have htl : (t ^ l : ℝ) ≠ 0 := pow_ne_zero _ ht.ne'
  rw [Real.rpow_sub ht, Real.rpow_natCast, div_eq_mul_inv, mul_comm, mul_smul, ← h, smul_smul,
    inv_mul_cancel₀ htl, one_smul]

omit [NormedSpace ℝ E] in
/-- The norms of `j` position directions followed by `l` frequency directions multiply to the
product of the norms of the two families. -/
private theorem prod_norm_append {j l : ℕ} (u : Fin j → E) (w : Fin l → E) :
    ∏ i, ‖Fin.append (fun i => ((u i, 0) : E × E)) (fun i => (0, w i)) i‖ =
      (∏ i, ‖u i‖) * ∏ i, ‖w i‖ := by
  simp [Fin.prod_univ_add, Prod.norm_def]

/-- The derivatives of a homogeneous symbol of degree `m` in `j` position directions and `l`
frequency directions are bounded by `C ‖ξ‖ ^ (m - l)` for positions in a compact set. -/
theorem exists_norm_iteratedFDeriv_le [ProperSpace E] {K : Set E} (hK : IsCompact K)
    (j l : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ξ ≠ 0 → ∀ (u : Fin j → E) (w : Fin l → E),
      ‖iteratedFDeriv ℝ (j + l) a.coefficient (x, ξ)
          (Fin.append (fun i => (u i, 0)) (fun i => (0, w i)))‖ ≤
        C * ‖ξ‖ ^ (m - l) * (∏ i, ‖u i‖) * ∏ i, ‖w i‖ := by
  have hsub : K ×ˢ sphere (0 : E) 1 ⊆ {p : E × E | p.2 ≠ 0} := fun p hp => by
    have := hp.2
    rw [mem_sphere_zero_iff_norm] at this
    exact ne_zero_of_norm_ne_zero (by simp [this])
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_sphere 0 1)).exists_bound_of_continuousOn
    ((a.continuousOn_iteratedFDeriv_coefficient (j + l)).mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ hξ u w => ?_⟩
  have hnξ : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set θ : E := ‖ξ‖⁻¹ • ξ
  have hθ : θ ≠ 0 := smul_ne_zero (inv_ne_zero hnξ.ne') hξ
  have hξθ : ξ = ‖ξ‖ • θ := by simp [θ, smul_smul, hnξ.ne']
  have hbound : ‖iteratedFDeriv ℝ (j + l) a.coefficient (x, θ)‖ ≤ max C 0 :=
    (hC (x, θ) ⟨hx, by simp [θ, norm_smul, hnξ.ne']⟩).trans (le_max_left _ _)
  have hop := (iteratedFDeriv ℝ (j + l) a.coefficient (x, θ)).le_opNorm
    (Fin.append (fun i => (u i, 0)) (fun i => (0, w i)))
  rw [prod_norm_append] at hop
  rw [hξθ, a.iteratedFDeriv_coefficient_smul_frequency_append hθ hnξ, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg hnξ.le _), ← hξθ]
  calc ‖ξ‖ ^ (m - l) * ‖iteratedFDeriv ℝ (j + l) a.coefficient (x, θ)
          (Fin.append (fun i => (u i, 0)) (fun i => (0, w i)))‖
      ≤ ‖ξ‖ ^ (m - l) * (max C 0 * ((∏ i, ‖u i‖) * ∏ i, ‖w i‖)) := by
        refine mul_le_mul_of_nonneg_left (hop.trans ?_) (Real.rpow_nonneg hnξ.le _)
        rw [← mul_assoc, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbound (by positivity))
          (by positivity)
    _ = max C 0 * ‖ξ‖ ^ (m - l) * (∏ i, ‖u i‖) * ∏ i, ‖w i‖ := by ring

end Derivatives

/-! ### Cutting off the zero frequency -/

section Cutoff

omit [NormedSpace ℝ E] in
/-- For `‖ξ‖ ≥ 1`, the power `‖ξ‖ ^ r` is bounded by a multiple of `⟨ξ⟩ ^ r`. -/
private theorem norm_rpow_le_one_add_norm_sq_rpow {ξ : E} (hξ : 1 ≤ ‖ξ‖) (r : ℝ) :
    ‖ξ‖ ^ r ≤ 2 ^ (|r| / 2) * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  have hs : 0 < ‖ξ‖ := one_pos.trans_le hξ
  have hsq : ‖ξ‖ ^ r = (‖ξ‖ ^ 2) ^ (r / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    ring_nf
  rw [hsq]
  rcases le_or_gt 0 r with hr | hr
  · calc (‖ξ‖ ^ 2) ^ (r / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ ≤ 2 ^ (|r| / 2) * (1 + ‖ξ‖ ^ 2) ^ (r / 2) :=
          le_mul_of_one_le_left (by positivity) (Real.one_le_rpow (by norm_num) (by positivity))
  · have h2 : (1 + ‖ξ‖ ^ 2) ^ (r / 2) ≥ (2 * ‖ξ‖ ^ 2) ^ (r / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at h2
    have h2r : (2 : ℝ) ^ (|r| / 2) * 2 ^ (r / 2) = 1 := by
      rw [abs_of_neg hr, ← Real.rpow_add (by norm_num), show -r / 2 + r / 2 = 0 by ring,
        Real.rpow_zero]
    calc (‖ξ‖ ^ 2) ^ (r / 2) = 2 ^ (|r| / 2) * (2 ^ (r / 2) * (‖ξ‖ ^ 2) ^ (r / 2)) := by
          rw [← mul_assoc, h2r, one_mul]
      _ ≤ 2 ^ (|r| / 2) * (1 + ‖ξ‖ ^ 2) ^ (r / 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)

omit [NormedSpace ℝ E] in
/-- For `‖ξ‖ ≤ 2`, the weight `⟨ξ⟩ ^ r` is bounded below by `5 ^ (-|r| / 2)`. -/
private theorem rpow_le_one_add_norm_sq_rpow {ξ : E} (hξ : ‖ξ‖ ≤ 2) (r : ℝ) :
    (5 : ℝ) ^ (-|r| / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  have h5 : 1 + ‖ξ‖ ^ 2 ≤ 5 := by nlinarith [norm_nonneg ξ]
  rcases le_or_gt 0 r with hr | hr
  · exact (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [abs_nonneg r])).trans
      (Real.one_le_rpow (by nlinarith [norm_nonneg ξ]) (by linarith))
  · rw [abs_of_neg hr, neg_neg]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h5 (by linarith)

/-- A smooth function on `E × E` satisfies, for positions in a compact set and frequencies in a
ball, every derivative estimate with the weight `⟨ξ⟩ ^ r`. -/
private theorem exists_norm_iteratedFDeriv_le_of_norm_le [ProperSpace E] {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] {f : E × E → A} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (k : ℕ) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ : E, ‖ξ‖ ≤ 2 →
      ‖iteratedFDeriv ℝ k f (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : E) 2)).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (mod_cast le_top)).continuousOn
  refine ⟨max C 0 / 5 ^ (-|r| / 2), by positivity, fun x hx ξ hξ => ?_⟩
  have h5 : (0 : ℝ) < 5 ^ (-|r| / 2) := by positivity
  calc ‖iteratedFDeriv ℝ k f (x, ξ)‖ ≤ max C 0 :=
        (hC (x, ξ) ⟨hx, by simpa using hξ⟩).trans (le_max_left _ _)
    _ = max C 0 / 5 ^ (-|r| / 2) * 5 ^ (-|r| / 2) := by field_simp
    _ ≤ max C 0 / 5 ^ (-|r| / 2) * (1 + ‖ξ‖ ^ 2) ^ (r / 2) :=
        mul_le_mul_of_nonneg_left (rpow_le_one_add_norm_sq_rpow hξ r) (by positivity)

variable (a : HomogeneousSymbol E V W m) (χ : FrequencyCutoff E)

/-- Multiplying a homogeneous symbol by a frequency cutoff gives a smooth function on all of
`E × E`. -/
theorem contDiff_frequencyCutoff_smul :
    ContDiff ℝ ∞ fun p : E × E => χ p.2 • a.coefficient p := by
  rw [contDiff_iff_contDiffAt]
  intro p
  rcases eq_or_ne p.2 0 with hp | hp
  · refine contDiffAt_const (c := (0 : V →L[ℂ] W)).congr_of_eventuallyEq ?_
    have : ‖p.2‖ < 1 := by simp [hp]
    filter_upwards [continuous_snd.continuousAt.eventually (χ.eventuallyEq_zero this)] with q hq
    simp [hq]
  · exact ((χ.contDiff.comp contDiff_snd).contDiffAt).smul (a.contDiffAt_coefficient hp)

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol of degree `m` satisfies the symbol
estimates of order `m`: its derivatives in `j` position directions and `l` frequency directions
are bounded by `C ⟨ξ⟩ ^ (m - l)` for positions in a compact set. -/
theorem exists_norm_iteratedFDeriv_frequencyCutoff_smul_le [ProperSpace E] {K : Set E}
    (hK : IsCompact K) (j l : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ (ξ : E) (u : Fin j → E) (w : Fin l → E),
      ‖iteratedFDeriv ℝ (j + l) (fun p : E × E => χ p.2 • a.coefficient p) (x, ξ)
          (Fin.append (fun i => (u i, 0)) (fun i => (0, w i)))‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) * (∏ i, ‖u i‖) * ∏ i, ‖w i‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_iteratedFDeriv_le_of_norm_le
    (a.contDiff_frequencyCutoff_smul χ) hK (j + l) (m - l)
  obtain ⟨C₂, hC₂, h₂⟩ := a.exists_norm_iteratedFDeriv_le hK j l
  refine ⟨max C₁ (C₂ * 2 ^ (|m - l| / 2)), le_max_of_le_left hC₁, fun x hx ξ u w => ?_⟩
  have hprod : 0 ≤ (∏ i, ‖u i‖) * ∏ i, ‖w i‖ := by positivity
  rw [mul_assoc _ (∏ i, ‖u i‖)]
  rcases le_or_gt ‖ξ‖ 2 with hξ | hξ
  · -- Near the zero frequency the cut-off term is smooth, so compactness bounds it.
    refine ((iteratedFDeriv ℝ (j + l) (fun p : E × E => χ p.2 • a.coefficient p)
      (x, ξ)).le_opNorm _).trans ?_
    rw [prod_norm_append]
    refine mul_le_mul_of_nonneg_right ((h₁ x hx ξ hξ).trans ?_) hprod
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- At large frequencies the cut-off term agrees with the homogeneous symbol.
    have hξ0 : ξ ≠ 0 := norm_pos_iff.mp (two_pos.trans hξ)
    have heq : (fun p : E × E => χ p.2 • a.coefficient p) =ᶠ[𝓝 (x, ξ)] a.coefficient := by
      filter_upwards [continuous_snd.continuousAt.eventually (χ.eventuallyEq_one hξ)] with q hq
      simp [hq]
    rw [heq.iteratedFDeriv ℝ (j + l) |>.eq_of_nhds]
    refine (h₂ x hx ξ hξ0 u w).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hprod
    calc C₂ * ‖ξ‖ ^ (m - l) ≤ C₂ * (2 ^ (|m - l| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2)) :=
          mul_le_mul_of_nonneg_left
            (norm_rpow_le_one_add_norm_sq_rpow (by linarith) (m - l)) hC₂
      _ = C₂ * 2 ^ (|m - l| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) := by ring
      _ ≤ max C₁ (C₂ * 2 ^ (|m - l| / 2)) * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Changing the frequency cutoff changes the cut-off term of a homogeneous symbol by a smoothing
term: for positions in a compact set, every derivative of the difference is bounded by
`C ⟨ξ⟩ ^ r`, for every real `r`. -/
theorem exists_norm_iteratedFDeriv_sub_frequencyCutoff_smul_le [ProperSpace E]
    (χ' : FrequencyCutoff E) {K : Set E} (hK : IsCompact K) (k : ℕ) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ : E,
      ‖iteratedFDeriv ℝ k
          (fun p : E × E => χ p.2 • a.coefficient p - χ' p.2 • a.coefficient p) (x, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_le_of_norm_le
    ((a.contDiff_frequencyCutoff_smul χ).sub (a.contDiff_frequencyCutoff_smul χ')) hK k r
  refine ⟨C, hC, fun x hx ξ => ?_⟩
  rcases le_or_gt ‖ξ‖ 2 with hξ | hξ
  · exact h x hx ξ hξ
  · -- Outside the ball of radius `2` both cutoffs equal `1`, so the difference vanishes nearby.
    have heq : (fun p : E × E => χ p.2 • a.coefficient p - χ' p.2 • a.coefficient p)
        =ᶠ[𝓝 (x, ξ)] 0 := by
      filter_upwards [continuous_snd.continuousAt.eventually (χ.eventuallyEq_one hξ),
        continuous_snd.continuousAt.eventually (χ'.eventuallyEq_one hξ)] with q hq hq'
      simp [hq, hq']
    rw [heq.iteratedFDeriv ℝ k |>.eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    positivity

end Cutoff

end HomogeneousSymbol

end NormedSpace

namespace HomogeneousSymbol

/-! ### Powers of the frequency norm -/

section NormRpow

variable [InnerProductSpace ℝ E]

open scoped Classical in
variable (E V) in
/-- The homogeneous symbol `‖ξ‖ ^ m` times the identity of `V`, of degree `m`, set to `0` at
`ξ = 0`. -/
def normRpow (m : ℝ) : HomogeneousSymbol E V V m where
  coefficient p := if p.2 = 0 then 0 else ‖p.2‖ ^ m • ContinuousLinearMap.id ℂ V
  coefficient_zero_frequency x := by simp
  contDiffOn_coefficient := by
    refine ContDiffOn.congr (f := fun p : E × E => ‖p.2‖ ^ m • ContinuousLinearMap.id ℂ V)
      (fun p hp => ?_) fun p hp => by simp [show p.2 ≠ 0 from hp]
    refine ContDiffAt.contDiffWithinAt ?_
    exact (((contDiffAt_norm ℝ hp).comp p contDiffAt_snd).rpow_const_of_ne
      (norm_ne_zero_iff.mpr hp)).smul contDiffAt_const
  coefficient_smul_frequency_of_ne_zero x ξ hξ t ht := by
    simp only [smul_eq_zero, ht.ne', hξ, or_self, ite_false, norm_smul,
      Real.norm_of_nonneg ht.le, Real.mul_rpow ht.le (norm_nonneg ξ), mul_smul]

@[simp]
theorem normRpow_coefficient_of_ne_zero (m : ℝ) {x ξ : E} (hξ : ξ ≠ 0) :
    (normRpow E V m).coefficient (x, ξ) = ‖ξ‖ ^ m • ContinuousLinearMap.id ℂ V := by
  simp [normRpow, hξ]

end NormRpow

end HomogeneousSymbol

end TauCeti
