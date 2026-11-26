/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.IteratedDeriv.Indicator
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.ContinuousLinearMapInverse
import TauCeti.Analysis.Complex.Sector.Bounds
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The normalized resolvent and the resolvent of a parameter-elliptic symbol

Let `p` be a symbol of order `d` with values in the endomorphisms of `V`, the symbol of an operator
`A` whose resolvent `(A - λ)⁻¹` is to be approximated. In the reciprocal parameter `r = 1 / λ` of
the weakly parameter-dependent calculus (`TauCeti.WeakParameterSymbol`), the first approximation
is the pointwise *normalized resolvent*

`(1 - r p(x, ξ))⁻¹ = -λ (p(x, ξ) - λ)⁻¹`.

This file shows that it is a weakly parameter-dependent symbol of frequency order `0` and
anisotropy `d`, as soon as `p` is *parameter-elliptic* on the set `R` of reciprocal parameters
(`TauCeti.Symbol.IsParameterElliptic`): for `r ∈ R` the values `1 - r p(x, ξ)` are invertible,
with

`‖(1 - r p(x, ξ))⁻¹‖ ≤ C (1 + ‖r‖ ⟨ξ⟩ ^ d)⁻¹`

for positions in each compact set, uniformly in `r ∈ R` and the frequency. This is the
parameter-ellipticity of Grubb and Seeley, written in the reciprocal parameter: the resolvent decays
like `(⟨ξ⟩ ^ d + ‖λ‖)⁻¹`.

* `TauCeti.WeakParameterSymbol.normalizedResolvent`: the weakly parameter-dependent symbol
  `(x, ξ, r) ↦ (1 - r p(x, ξ))⁻¹`, extended by zero outside `R`. It is a two-sided inverse of
  `1 - r p(x, ξ)` for `r ∈ R`
  (`TauCeti.WeakParameterSymbol.comp_coefficient_normalizedResolvent`,
  `TauCeti.WeakParameterSymbol.coefficient_normalizedResolvent_comp`).
* `TauCeti.WeakParameterSymbol.iteratedDeriv_coefficient_normalizedResolvent`: its `j`-th
  derivative in the parameter is `j! p(x, ξ) ^ j ((1 - r p(x, ξ))⁻¹) ^ (j + 1)`, which therefore
  has frequency order `d j`.
* `TauCeti.WeakParameterSymbol.coefficient_normalizedResolvent_inv`: at the spectral parameter
  `λ = r⁻¹` it is `-λ (p(x, ξ) - λ)⁻¹`.
* `TauCeti.WeakParameterSymbol.resolvent`: the resolvent symbol `(λ - p(x, ξ))⁻¹`, that is
  `r (1 - r p(x, ξ))⁻¹`, extended by zero outside `R`. It is a weakly parameter-dependent symbol of
  frequency order `-d` and anisotropy `d`: one factor `r` turns the normalized resolvent, of size
  `(1 + ‖r‖ ⟨ξ⟩ ^ d)⁻¹`, into a symbol of size `⟨ξ⟩ ^ (-d)`. Its `(j + 1)`-th parameter derivative
  is `(j + 1)! p(x, ξ) ^ j ((1 - r p(x, ξ))⁻¹) ^ (j + 2)`
  (`TauCeti.WeakParameterSymbol.iteratedDeriv_succ_coefficient_resolvent`), and it inverts
  `1 - r p(x, ξ)` up to the factor `r` (`TauCeti.WeakParameterSymbol.coefficient_resolvent_comp`,
  `TauCeti.WeakParameterSymbol.comp_coefficient_resolvent`). Composing with it lowers the frequency
  order by `d` while absorbing a factor `r`, which is how the correction terms of the parametrix of
  `1 - r p` are built (`TauCeti.WeakParameterSymbol.leftNormalizedResolventTerms`).
* `TauCeti.Symbol.isParameterElliptic_of_coefficient_eq_smul`: an elliptic scalar symbol
  `w(x, ξ) • id` with `w ≥ 0` is parameter-elliptic on every sector `Re r ≤ c ‖r‖` with `c < 1`.
* `TauCeti.Symbol.isParameterElliptic_besselPotential`: in particular the Bessel weight
  `⟨ξ / 2π⟩ ^ d` of every real order `d` (`TauCeti.Symbol.besselPotential`) is, so that the
  normalized resolvent of the Bessel potential `(1 - Δ / 4π²) ^ (d / 2)` is a weakly
  parameter-dependent symbol.

## Implementation notes

The estimates are proved at one point `(x, ξ)` at a time, after dilating the frequency by
`t = ⟨ξ⟩`. The derivatives at `(0, 0)` of `(y, v) ↦ 1 - r p(x + y, ξ + t v)` are of the size
`s = 1 + ‖r‖ ⟨ξ⟩ ^ d` of the function itself, because each frequency derivative of `p` gains a
factor `⟨ξ⟩⁻¹` which the dilation compensates (`TauCeti.mixedDeriv_comp_add_smul`). By
parameter-ellipticity its inverse at `(0, 0)` has size `1 / s`, so the derivatives of the inverse
have size `1 / s ≤ 1` there (`TauCeti.exists_norm_iteratedFDeriv_clm_inverse_le`), with constants
independent of `r`, `x` and `ξ`. Undoing the dilation gives the symbol estimates of order `0`, and
the Leibniz rule those of the parameter derivatives `j! p ^ j ((1 - r p)⁻¹) ^ (j + 1)`, of order
`d j`. For the resolvent, the bound `1 / s` on the derivatives of the dilated inverse is kept:
`‖r‖ / s ≤ ⟨ξ⟩ ^ (-d)` gives the estimates of order `-d`.

## References

* G. Grubb and R. T. Seeley, *Weakly parametric pseudodifferential operators and Atiyah–Patodi–
  Singer boundary problems*, Invent. Math. 121 (1995), 481–529, §1.
* G. Grubb and L. Hansen, *Complex powers of resolvents of pseudodifferential operators*,
  Comm. Partial Differential Equations 27 (2002), Definition 2.1 and §4.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology Nat Real

namespace TauCeti

variable {n : ℕ}

/-! ### Parameter-elliptic symbols -/

namespace Symbol

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℝ}

/-- A symbol `p` of order `d` with values in the endomorphisms of `V` is **parameter-elliptic** on
a set `R` of reciprocal spectral parameters `r = 1 / λ` if, for every `r ∈ R`, the values
`1 - r p(x, ξ)` are invertible with
`‖(1 - r p(x, ξ))⁻¹‖ ≤ C (1 + ‖r‖ ⟨ξ⟩ ^ d)⁻¹`, where `⟨ξ⟩ = (1 + ‖ξ‖²) ^ (1 / 2)` and the constant
`C` depends only on a compact set containing the position `x`, not on `ξ` or `r`. -/
def IsParameterElliptic (p : Symbol n V V d) (R : Set ℂ) : Prop :=
  ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, ∀ r ∈ R,
    (1 - r • p.coefficient (x, ξ)).IsInvertible ∧
      (1 + ‖r‖ * (1 + ‖ξ‖ ^ 2) ^ (d / 2)) * ‖(1 - r • p.coefficient (x, ξ)).inverse‖ ≤ C

theorem isParameterElliptic_iff {p : Symbol n V V d} {R : Set ℂ} :
    p.IsParameterElliptic R ↔ ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ,
      ∀ r ∈ R, (1 - r • p.coefficient (x, ξ)).IsInvertible ∧
        (1 + ‖r‖ * (1 + ‖ξ‖ ^ 2) ^ (d / 2)) * ‖(1 - r • p.coefficient (x, ξ)).inverse‖ ≤ C :=
  Iff.rfl

variable {p : Symbol n V V d} {R R' : Set ℂ}

theorem IsParameterElliptic.mono (hp : p.IsParameterElliptic R) (h : R' ⊆ R) :
    p.IsParameterElliptic R' := fun K hK => (hp K hK).imp fun _ hC x hx ξ r hr => hC x hx ξ r (h hr)

/-- For a parameter-elliptic symbol, `1 - r p(x, ξ)` is invertible at every point, for `r ∈ R`. -/
theorem IsParameterElliptic.isInvertible (hp : p.IsParameterElliptic R) {r : ℂ} (hr : r ∈ R)
    (q : CoordinateSpace n × CoordinateSpace n) : (1 - r • p.coefficient q).IsInvertible := by
  obtain ⟨C, hC⟩ := hp {q.1} isCompact_singleton
  exact (hC q.1 rfl q.2 r hr).1

end Symbol

/-! ### Estimates for the normalized resolvent -/

section Estimates

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {d : ℝ}
  {p : Symbol n V V d} {R : Set ℂ}

/-- The frequency dilation `(y, v) ↦ (x + y, ξ + t v)` is smooth. -/
private theorem contDiff_dilate (x ξ : CoordinateSpace n) (t : ℝ) :
    ContDiff ℝ ∞ fun q : CoordinateSpace n × CoordinateSpace n => (x + q.1, ξ + t • q.2) :=
  (contDiff_const.add contDiff_fst).prodMk (contDiff_const.add (contDiff_snd.const_smul t))

/-- With `t = ⟨ξ⟩`, `t ^ i * (1 + ‖ξ‖²) ^ ((d - i) / 2) = (1 + ‖ξ‖²) ^ (d / 2)`. -/
private theorem japaneseBracket_pow_mul_rpow (ξ : CoordinateSpace n) (i : ℕ) (d : ℝ) :
    ((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ i * (1 + ‖ξ‖ ^ 2) ^ ((d - i) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ (d / 2) := by
  rw [one_add_norm_sq_rpow_one_div_two_pow, ← one_add_norm_sq_rpow_add, add_sub_cancel]

omit [CompleteSpace V] in
/-- **Dilated symbol estimates.** With `t = ⟨ξ⟩`, the derivatives of order at most `k` at `(0, 0)`
of `(y, v) ↦ p(x + y, ξ + t v)` are bounded by `S ⟨ξ⟩ ^ d`, uniformly for `x ∈ K`. -/
private theorem exists_norm_iteratedFDeriv_dilate_le (p : Symbol n V V d)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ S, 0 ≤ S ∧ ∀ x ∈ K, ∀ ξ, ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (fun q : CoordinateSpace n × CoordinateSpace n =>
          p.coefficient (x + q.1, ξ + (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) • q.2)) 0‖ ≤
        S * (1 + ‖ξ‖ ^ 2) ^ (d / 2) := by
  choose C hC0 hC using fun α β => p.exists_bound K hK α β
  let c : (i : ℕ) → (Fin i → Fin n ⊕ Fin n) → ℝ := fun _ w =>
    C ((List.ofFn w).filterMap Sum.getLeft?) ((List.ofFn w).filterMap Sum.getRight?)
  refine ⟨∑ i ∈ Finset.range (k + 1), ∑ w, c i w,
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => hC0 _ _, fun x hx ξ i hi => ?_⟩
  set t : ℝ := (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)
  have ht : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  have hsmooth : ContDiff ℝ ∞ fun q : CoordinateSpace n × CoordinateSpace n =>
      p.coefficient (x + q.1, ξ + t • q.2) :=
    p.contDiff_coefficient.comp (contDiff_dilate x ξ t)
  refine (norm_iteratedFDeriv_le_sum_mixedDeriv (hsmooth.of_le (by exact_mod_cast le_top)) 0).trans
    ?_
  calc ∑ w : Fin i → Fin n ⊕ Fin n,
        ‖mixedDeriv ((List.ofFn w).filterMap Sum.getLeft?) ((List.ofFn w).filterMap Sum.getRight?)
          (fun q : CoordinateSpace n × CoordinateSpace n =>
            p.coefficient (x + q.1, ξ + t • q.2)) (0 : CoordinateSpace n × CoordinateSpace n).1
            (0 : CoordinateSpace n × CoordinateSpace n).2‖
      ≤ ∑ w : Fin i → Fin n ⊕ Fin n, c i w * (1 + ‖ξ‖ ^ 2) ^ (d / 2) := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [Prod.fst_zero, Prod.snd_zero, mixedDeriv_comp_add_smul
          (p.contDiff_coefficient.of_le (by exact_mod_cast le_top)), norm_smul, Real.norm_eq_abs,
          abs_pow, abs_of_pos ht, ← japaneseBracket_pow_mul_rpow ξ _ d, mul_left_comm]
        gcongr
        exact hC _ _ x hx ξ
    _ = (∑ w, c i w) * (1 + ‖ξ‖ ^ 2) ^ (d / 2) := (Finset.sum_mul ..).symm
    _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (f := fun i => ∑ w, c i w)
          (fun i _ => Finset.sum_nonneg fun w _ => hC0 _ _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

omit [CompleteSpace V] in
/-- If the derivatives of order at most `k` of `P` at `y` are bounded by `S T`, those of
`1 - r P` are bounded by `(1 + S) (1 + ‖r‖ T)`. -/
private theorem norm_iteratedFDeriv_one_sub_smul_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {P : E → V →L[ℂ] V} (hP : ContDiff ℝ ∞ P) {y : E} {k : ℕ} {S T : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hPb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i P y‖ ≤ S * T) (r : ℂ) :
    ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun q => 1 - r • P q) y‖ ≤ (1 + S) * (1 + ‖r‖ * T) := by
  intro i hi
  have hsub : iteratedFDeriv ℝ i (fun q => 1 - r • P q) y =
      iteratedFDeriv ℝ i (fun _ : E => (1 : V →L[ℂ] V)) y - r • iteratedFDeriv ℝ i P y := by
    rw [fun_iteratedFDeriv_sub_apply contDiff_const.contDiffAt
      ((hP.const_smul r).of_le (by exact_mod_cast le_top)).contDiffAt,
      iteratedFDeriv_const_smul_apply' ((hP.of_le (by exact_mod_cast le_top)).contDiffAt)]
  have hone : ‖iteratedFDeriv ℝ i (fun _ : E => (1 : V →L[ℂ] V)) y‖ ≤ 1 :=
    (norm_iteratedFDeriv_const_le i _ y).trans ContinuousLinearMap.norm_one_le
  rw [hsub]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul]
  have : ‖r‖ * ‖iteratedFDeriv ℝ i P y‖ ≤ ‖r‖ * (S * T) := by gcongr; exact hPb i hi
  nlinarith [norm_nonneg r, mul_nonneg (norm_nonneg r) hT]

/-- **Dilated estimates for the inverse.** With `t = ⟨ξ⟩`, the derivatives of order at most `k`
at `(0, 0)` of `(y, v) ↦ (1 - r p(x + y, ξ + t v))⁻¹` are bounded by `c / (1 + ‖r‖ ⟨ξ⟩ ^ d)`,
uniformly for `x ∈ K`, all `ξ` and `r ∈ R`: by parameter-ellipticity the inverse at `(0, 0)` is of
size `1 / s` for the size `s = 1 + ‖r‖ ⟨ξ⟩ ^ d` of the derivatives of `1 - r p` there. -/
private theorem exists_norm_iteratedFDeriv_dilate_inverse_le (hp : p.IsParameterElliptic R)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ c, 0 ≤ c ∧ ∀ x ∈ K, ∀ ξ, ∀ r ∈ R, ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (fun q : CoordinateSpace n × CoordinateSpace n =>
          (1 - r • p.coefficient (x + q.1, ξ + (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) • q.2)).inverse) 0‖ ≤
        c / (1 + ‖r‖ * (1 + ‖ξ‖ ^ 2) ^ (d / 2)) := by
  obtain ⟨S, hS0, hS⟩ := exists_norm_iteratedFDeriv_dilate_le p hK k
  obtain ⟨B, hB⟩ := hp K hK
  obtain ⟨c, hc⟩ := exists_norm_iteratedFDeriv_clm_inverse_le
    (E := CoordinateSpace n × CoordinateSpace n) (V := V) (W := V) k (1 + S) B
  refine ⟨|c|, abs_nonneg c, fun x hx ξ r hr i hi => ?_⟩
  set T : ℝ := (1 + ‖ξ‖ ^ 2) ^ (d / 2)
  set s : ℝ := 1 + ‖r‖ * T
  set t : ℝ := (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)
  set P : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] V :=
    fun q => p.coefficient (x + q.1, ξ + t • q.2)
  have hP : ContDiff ℝ ∞ P := p.contDiff_coefficient.comp (contDiff_dilate x ξ t)
  have hF0 : 1 - r • P 0 = 1 - r • p.coefficient (x, ξ) := by simp [P]
  have hFinvb : ‖(1 - r • P 0).inverse‖ ≤ B / s := by
    rw [le_div_iff₀ (by positivity), mul_comm, hF0]
    exact (hB x hx ξ r hr).2
  have h := hc (fun q => 1 - r • P q) univ 0 s (by positivity) isOpen_univ (mem_univ _)
    (contDiff_const.sub (hP.const_smul r)).contDiffOn (fun q _ => hp.isInvertible hr _)
    (norm_iteratedFDeriv_one_sub_smul_le hP hS0 (by positivity) (hS x hx ξ) r) hFinvb i hi
  exact h.trans (div_le_div_of_nonneg_right (le_abs_self c) (by positivity))

/-- For `r ∈ R`, the inverse `(x, ξ) ↦ (1 - r p(x, ξ))⁻¹` of a parameter-elliptic symbol is
smooth. -/
private theorem contDiff_inverse_one_sub_smul (hp : p.IsParameterElliptic R) {r : ℂ} (hr : r ∈ R) :
    ContDiff ℝ ∞ fun q => (1 - r • p.coefficient q).inverse :=
  (contDiff_const.sub (p.contDiff_coefficient.const_smul r)).clm_inverse
    fun q => hp.isInvertible hr q

/-- **Symbol estimates for products of powers, uniformly in the parameter.** For a
parameter-elliptic symbol `p` of order `d`, the functions
`(x, ξ) ↦ p(x, ξ) ^ i ((1 - r p(x, ξ))⁻¹) ^ l` satisfy the symbol estimates of order `d i` on every
compact set of positions, uniformly in `r ∈ R`. -/
private theorem exists_norm_mixedDeriv_pow_mul_inverse_pow_le (hp : p.IsParameterElliptic R)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (i l : ℕ) (α β : List (Fin n)) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ K, ∀ ξ, ∀ r ∈ R,
      ‖mixedDeriv α β (fun q => p.coefficient q ^ i * (1 - r • p.coefficient q).inverse ^ l)
          x ξ‖ ≤ M * (1 + ‖ξ‖ ^ 2) ^ ((d * i - β.length) / 2) := by
  set k := α.length + β.length
  obtain ⟨S, hS0, hS⟩ := exists_norm_iteratedFDeriv_dilate_le p hK k
  obtain ⟨c, hc0, hc⟩ := exists_norm_iteratedFDeriv_dilate_inverse_le hp hK k
  set M := (2 : ℝ) ^ k * (2 ^ k * S) ^ i * (2 ^ k * c) ^ l
  refine ⟨M, by positivity, fun x hx ξ r hr => ?_⟩
  set u : ℝ := 1 + ‖ξ‖ ^ 2
  have hu : 0 < u := by positivity
  set t : ℝ := u ^ ((1 : ℝ) / 2)
  have ht : 0 < t := Real.rpow_pos_of_pos hu _
  set g : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] V :=
    fun q => p.coefficient q ^ i * (1 - r • p.coefficient q).inverse ^ l
  have hinv := contDiff_inverse_one_sub_smul hp hr
  have hg : ContDiff ℝ ∞ g := (p.contDiff_coefficient.pow i).mul (hinv.pow l)
  -- The dilation of `g` is a product of the dilations of `p` and of the inverse, whose derivatives
  -- at `0` are of size `⟨ξ⟩ ^ d` and at most `c`; by the Leibniz rule its derivatives are of size
  -- `⟨ξ⟩ ^ (d i)`.
  have hD := contDiff_dilate x ξ t
  have hP := (p.contDiff_coefficient.comp hD).of_le (m := k) (by exact_mod_cast le_top)
  have hG := (hinv.comp hD).of_le (m := k) (by exact_mod_cast le_top)
  have hc' : ∀ i' ≤ k, ‖iteratedFDeriv ℝ i' ((fun q => (1 - r • p.coefficient q).inverse) ∘
      fun q : CoordinateSpace n × CoordinateSpace n => (x + q.1, ξ + t • q.2)) 0‖ ≤ c :=
    fun i' hi' => (hc x hx ξ r hr i' hi').trans
      (div_le_self hc0 (le_add_of_nonneg_right (by positivity)))
  have hprod := (hP.pow i).norm_iteratedFDeriv_mul_le_two_pow (hG.pow l)
    (hP.norm_iteratedFDeriv_pow_le_two_pow ContinuousLinearMap.norm_one_le (hS x hx ξ) i)
    (hG.norm_iteratedFDeriv_pow_le_two_pow ContinuousLinearMap.norm_one_le hc' l) k le_rfl
  -- Undo the dilation: each frequency derivative costs a factor `t = ⟨ξ⟩`.
  have hkey : t ^ β.length * ‖mixedDeriv α β g x ξ‖ ≤ M * (u ^ (d / 2)) ^ i :=
    (pow_mul_norm_mixedDeriv_le_norm_iteratedFDeriv_comp_add_smul
      (hg.of_le (by exact_mod_cast le_top)) x ξ ht.le).trans
      (hprod.trans_eq (by simp only [M]; ring))
  have hTi : (u ^ (d / 2)) ^ i = u ^ ((d * i - β.length) / 2) * t ^ β.length := by
    simp only [t]
    rw [← Real.rpow_natCast (u ^ (d / 2)) i, ← Real.rpow_mul hu.le,
      ← Real.rpow_natCast (u ^ ((1 : ℝ) / 2)) β.length, ← Real.rpow_mul hu.le,
      ← Real.rpow_add hu]
    congr 1
    ring
  rw [hTi] at hkey
  exact le_of_mul_le_mul_left (hkey.trans_eq (by ring)) (pow_pos ht _)

/-- **Symbol estimates of order `-d` for `r (1 - r p)⁻¹`, uniformly in the parameter.** For a
parameter-elliptic symbol `p` of order `d`, the function `(x, ξ) ↦ r (1 - r p(x, ξ))⁻¹` satisfies
the symbol estimates of order `-d` on every compact set of positions, uniformly in `r ∈ R`: the
derivatives of the dilated inverse are of size `1 / (1 + ‖r‖ ⟨ξ⟩ ^ d)`, and
`‖r‖ / (1 + ‖r‖ ⟨ξ⟩ ^ d) ≤ ⟨ξ⟩ ^ (-d)`. -/
private theorem exists_norm_mixedDeriv_smul_inverse_le (hp : p.IsParameterElliptic R)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ K, ∀ ξ, ∀ r ∈ R,
      ‖mixedDeriv α β (fun q => r • (1 - r • p.coefficient q).inverse) x ξ‖ ≤
        M * (1 + ‖ξ‖ ^ 2) ^ ((-d - β.length) / 2) := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_iteratedFDeriv_dilate_inverse_le hp hK (α.length + β.length)
  refine ⟨c, hc0, fun x hx ξ r hr => ?_⟩
  set u : ℝ := 1 + ‖ξ‖ ^ 2
  have hu : 0 < u := by positivity
  set t : ℝ := u ^ ((1 : ℝ) / 2)
  have ht : 0 < t := Real.rpow_pos_of_pos hu _
  set T : ℝ := u ^ (d / 2)
  have hT : 0 < T := Real.rpow_pos_of_pos hu _
  have hinv := contDiff_inverse_one_sub_smul hp hr
  set D := ‖mixedDeriv α β (fun q => (1 - r • p.coefficient q).inverse) x ξ‖
  have hD : t ^ β.length * D ≤ c / (1 + ‖r‖ * T) :=
    (pow_mul_norm_mixedDeriv_le_norm_iteratedFDeriv_comp_add_smul
      (hinv.of_le (by exact_mod_cast le_top)) x ξ ht.le).trans
      (hc x hx ξ r hr _ le_rfl)
  -- `‖r‖ / (1 + ‖r‖ T) ≤ 1 / T`
  have hrD : T * (‖r‖ * (t ^ β.length * D)) ≤ c := by
    have h1 : ‖r‖ * (t ^ β.length * D) ≤ ‖r‖ * (c / (1 + ‖r‖ * T)) :=
      mul_le_mul_of_nonneg_left hD (norm_nonneg r)
    have h2 : T * (‖r‖ * (c / (1 + ‖r‖ * T))) ≤ c := by
      rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg r]
    exact (mul_le_mul_of_nonneg_left h1 hT.le).trans h2
  have hexp : u ^ ((-d - β.length) / 2) * (T * t ^ β.length) = 1 := by
    simp only [T, t]
    rw [← Real.rpow_natCast (u ^ ((1 : ℝ) / 2)) β.length, ← Real.rpow_mul hu.le,
      ← Real.rpow_add hu, ← Real.rpow_add hu]
    convert Real.rpow_zero u using 2
    ring
  have hsmul : (fun q => r • (1 - r • p.coefficient q).inverse) =
      r • fun q => (1 - r • p.coefficient q).inverse := rfl
  rw [hsmul, mixedDeriv_const_smul, norm_smul]
  calc ‖r‖ * D = u ^ ((-d - β.length) / 2) * (T * t ^ β.length) * (‖r‖ * D) := by
        rw [hexp, one_mul]
    _ = u ^ ((-d - β.length) / 2) * (T * (‖r‖ * (t ^ β.length * D))) := by ring
    _ ≤ c * u ^ ((-d - β.length) / 2) := by
        rw [mul_comm c]
        exact mul_le_mul_of_nonneg_left hrD (by positivity)

end Estimates

/-! ### The normalized resolvent -/

namespace WeakParameterSymbol

variable {R : TopologicalSpace.Opens ℂ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V] {d : ℝ}

/-- The `j`-th parameter derivative of `r ↦ (1 - r P)⁻¹` on `R`, extended by zero outside `R`, is
`j! P ^ j ((1 - r P)⁻¹) ^ (j + 1)` at a parameter `r ∈ R` where `1 - r P` is invertible. -/
private theorem iteratedDeriv_indicator_inverse_one_sub_smul (P : V →L[ℂ] V) (j : ℕ) {r : ℂ}
    (hr : r ∈ R) (hP : (1 - r • P).IsInvertible) :
    iteratedDeriv j ((R : Set ℂ).indicator fun s => (1 - s • P).inverse) r =
      (j ! : ℂ) • (P ^ j * (1 - r • P).inverse ^ (j + 1)) := by
  rw [iteratedDeriv_indicator_of_mem R.isOpen hr, ← ContinuousLinearMap.ringInverse_eq_inverse]
  exact iteratedDeriv_ringInverse_one_sub_smul P j
    (ContinuousLinearMap.isInvertible_iff_isUnit.1 hP)

/-- The **normalized resolvent** `(1 - r p(x, ξ))⁻¹` of a parameter-elliptic symbol `p` of order
`d` (`TauCeti.Symbol.IsParameterElliptic`), on an open set `R` of reciprocal spectral parameters
`r = 1 / λ` and extended by zero outside `R`. At the spectral parameter `λ` it is
`-λ (p(x, ξ) - λ)⁻¹` (`TauCeti.WeakParameterSymbol.coefficient_normalizedResolvent_inv`). It is a
weakly parameter-dependent symbol of frequency order `0` and anisotropy `d`: its `j`-th derivative
in `r` is `j! p(x, ξ) ^ j ((1 - r p(x, ξ))⁻¹) ^ (j + 1)`
(`TauCeti.WeakParameterSymbol.iteratedDeriv_coefficient_normalizedResolvent`), of order `d j`
uniformly in `r ∈ R`. -/
def normalizedResolvent (p : Symbol n V V d) (hp : p.IsParameterElliptic R) :
    WeakParameterSymbol n R V V d 0 where
  coefficient q := (R : Set ℂ).indicator fun r => (1 - r • p.coefficient q).inverse
  contDiffOn_coefficient q := by
    refine ContDiffOn.congr (f := fun r => (1 - r • p.coefficient q).inverse) ?_
      fun _ hr => indicator_of_mem hr _
    exact (contDiffOn_const.sub (contDiffOn_id.smul contDiffOn_const)).clm_inverse
      fun r hr => hp.isInvertible hr q
  coefficient_of_notMem q r hr := indicator_of_notMem hr _
  contDiff_iteratedDeriv j r hr := by
    simp only [iteratedDeriv_indicator_inverse_one_sub_smul _ j hr (hp.isInvertible hr _)]
    exact ((p.contDiff_coefficient.pow j).mul
      ((contDiff_inverse_one_sub_smul hp hr).pow (j + 1))).const_smul _
  exists_bound K hK j α β := by
    obtain ⟨M, hM0, hM⟩ := exists_norm_mixedDeriv_pow_mul_inverse_pow_le hp hK j (j + 1) α β
    refine ⟨j ! * M, by positivity, fun x hx ξ r hr => ?_⟩
    simp only [iteratedDeriv_indicator_inverse_one_sub_smul _ j hr (hp.isInvertible hr _)]
    have hsmul : (fun q : CoordinateSpace n × CoordinateSpace n =>
        (j ! : ℂ) • (p.coefficient q ^ j * (1 - r • p.coefficient q).inverse ^ (j + 1))) =
        (j ! : ℂ) • fun q => p.coefficient q ^ j * (1 - r • p.coefficient q).inverse ^ (j + 1) :=
      rfl
    rw [hsmul, mixedDeriv_const_smul, norm_smul, Complex.norm_natCast, zero_add, mul_assoc]
    gcongr
    exact hM x hx ξ r hr

variable {p : Symbol n V V d} {hp : p.IsParameterElliptic R}

@[simp]
theorem coefficient_normalizedResolvent (q : CoordinateSpace n × CoordinateSpace n) {r : ℂ}
    (hr : r ∈ R) :
    (normalizedResolvent p hp).coefficient q r = (1 - r • p.coefficient q).inverse :=
  indicator_of_mem (s := (R : Set ℂ)) hr fun r => (1 - r • p.coefficient q).inverse

/-- The normalized resolvent is a right inverse of `1 - r p(x, ξ)` for `r ∈ R`. -/
theorem comp_coefficient_normalizedResolvent (q : CoordinateSpace n × CoordinateSpace n) {r : ℂ}
    (hr : r ∈ R) :
    (1 - r • p.coefficient q) ∘L (normalizedResolvent p hp).coefficient q r =
      ContinuousLinearMap.id ℂ V := by
  rw [coefficient_normalizedResolvent q hr]
  exact (hp.isInvertible hr q).self_comp_inverse

/-- The normalized resolvent is a left inverse of `1 - r p(x, ξ)` for `r ∈ R`. -/
theorem coefficient_normalizedResolvent_comp (q : CoordinateSpace n × CoordinateSpace n) {r : ℂ}
    (hr : r ∈ R) :
    (normalizedResolvent p hp).coefficient q r ∘L (1 - r • p.coefficient q) =
      ContinuousLinearMap.id ℂ V := by
  rw [coefficient_normalizedResolvent q hr]
  exact (hp.isInvertible hr q).inverse_comp_self

/-- The parameter derivatives of the normalized resolvent:
`∂_r^j (1 - r p(x, ξ))⁻¹ = j! p(x, ξ) ^ j ((1 - r p(x, ξ))⁻¹) ^ (j + 1)`. -/
theorem iteratedDeriv_coefficient_normalizedResolvent (j : ℕ)
    (q : CoordinateSpace n × CoordinateSpace n) {r : ℂ} (hr : r ∈ R) :
    iteratedDeriv j ((normalizedResolvent p hp).coefficient q) r =
      (j ! : ℂ) • (p.coefficient q ^ j * (1 - r • p.coefficient q).inverse ^ (j + 1)) :=
  iteratedDeriv_indicator_inverse_one_sub_smul _ j hr (hp.isInvertible hr q)

/-- At the spectral parameter `λ ≠ 0` with `λ⁻¹ ∈ R`, the normalized resolvent is
`-λ (p(x, ξ) - λ)⁻¹`, that is `-λ` times the resolvent of `p(x, ξ)`. -/
theorem coefficient_normalizedResolvent_inv (q : CoordinateSpace n × CoordinateSpace n) {μ : ℂ}
    (hμ : μ⁻¹ ∈ R) (hμ0 : μ ≠ 0) :
    (normalizedResolvent p hp).coefficient q μ⁻¹ = (-μ) • (p.coefficient q - μ • 1).inverse := by
  have h : 1 - μ⁻¹ • p.coefficient q = (-μ⁻¹) • (p.coefficient q - μ • 1) := by
    simp [smul_sub, smul_smul, hμ0, neg_add_eq_sub]
  rw [coefficient_normalizedResolvent q hμ, h, ContinuousLinearMap.inverse_smul, inv_neg, inv_inv]

/-! ### The resolvent -/

/-- The `(j + 1)`-th parameter derivative of `r ↦ r (1 - r P)⁻¹` on `R`, extended by zero outside
`R`, is `(j + 1)! P ^ j ((1 - r P)⁻¹) ^ (j + 2)` at a parameter `r ∈ R` where `1 - r P` is
invertible. -/
private theorem iteratedDeriv_succ_indicator_smul_inverse_one_sub_smul (P : V →L[ℂ] V) (j : ℕ)
    {r : ℂ} (hr : r ∈ R) (hP : (1 - r • P).IsInvertible) :
    iteratedDeriv (j + 1) ((R : Set ℂ).indicator fun s => s • (1 - s • P).inverse) r =
      ((j + 1)! : ℂ) • (P ^ j * (1 - r • P).inverse ^ (j + 2)) := by
  rw [iteratedDeriv_indicator_of_mem R.isOpen hr, ← ContinuousLinearMap.ringInverse_eq_inverse]
  exact iteratedDeriv_succ_smul_ringInverse_one_sub_smul P j
    (ContinuousLinearMap.isInvertible_iff_isUnit.1 hP)

/-- The **resolvent** `(λ - p(x, ξ))⁻¹ = r (1 - r p(x, ξ))⁻¹` of a parameter-elliptic symbol `p` of
order `d` (`TauCeti.Symbol.IsParameterElliptic`), written in the reciprocal spectral parameter
`r = 1 / λ` on an open set `R` and extended by zero outside `R`; at `r = 0`, that is `λ = ∞`, it is
`0`. At the spectral parameter `λ` it is `(λ - p(x, ξ))⁻¹`
(`TauCeti.WeakParameterSymbol.coefficient_resolvent_inv`), and it is `r` times the normalized
resolvent (`TauCeti.WeakParameterSymbol.coefficient_resolvent_eq_smul`). It is a weakly
parameter-dependent symbol of frequency order `-d` and anisotropy `d`: its `(j + 1)`-th derivative
in `r` is `(j + 1)! p(x, ξ) ^ j ((1 - r p(x, ξ))⁻¹) ^ (j + 2)`
(`TauCeti.WeakParameterSymbol.iteratedDeriv_succ_coefficient_resolvent`), of order `d j`, uniformly
in `r ∈ R`. -/
def resolvent (p : Symbol n V V d) (hp : p.IsParameterElliptic R) :
    WeakParameterSymbol n R V V d (-d) where
  coefficient q := (R : Set ℂ).indicator fun r => r • (1 - r • p.coefficient q).inverse
  contDiffOn_coefficient q := by
    refine ContDiffOn.congr (f := fun r => r • (1 - r • p.coefficient q).inverse) ?_
      fun _ hr => indicator_of_mem hr _
    exact contDiffOn_id.smul ((contDiffOn_const.sub
      (contDiffOn_id.smul contDiffOn_const)).clm_inverse fun r hr => hp.isInvertible hr q)
  coefficient_of_notMem q r hr := indicator_of_notMem hr _
  contDiff_iteratedDeriv j r hr := by
    have hinv := contDiff_inverse_one_sub_smul hp hr
    rcases j with _ | j
    · simp only [iteratedDeriv_zero, indicator_of_mem hr]
      exact hinv.const_smul r
    · simp only [iteratedDeriv_succ_indicator_smul_inverse_one_sub_smul _ j hr
        (hp.isInvertible hr _)]
      exact ((p.contDiff_coefficient.pow j).mul (hinv.pow (j + 2))).const_smul _
  exists_bound K hK j α β := by
    rcases j with _ | j
    · obtain ⟨M, hM0, hM⟩ := exists_norm_mixedDeriv_smul_inverse_le hp hK α β
      refine ⟨M, hM0, fun x hx ξ r hr => ?_⟩
      simp only [iteratedDeriv_zero, indicator_of_mem hr, Nat.cast_zero, mul_zero, add_zero]
      exact (hM x hx ξ r hr).trans_eq (by ring_nf)
    · obtain ⟨M, hM0, hM⟩ := exists_norm_mixedDeriv_pow_mul_inverse_pow_le hp hK j (j + 2) α β
      refine ⟨(j + 1)! * M, by positivity, fun x hx ξ r hr => ?_⟩
      simp only [iteratedDeriv_succ_indicator_smul_inverse_one_sub_smul _ j hr
        (hp.isInvertible hr _)]
      have hsmul : (fun q : CoordinateSpace n × CoordinateSpace n =>
          ((j + 1)! : ℂ) • (p.coefficient q ^ j * (1 - r • p.coefficient q).inverse ^ (j + 2))) =
          ((j + 1)! : ℂ) • fun q =>
            p.coefficient q ^ j * (1 - r • p.coefficient q).inverse ^ (j + 2) :=
        rfl
      rw [hsmul, mixedDeriv_const_smul, norm_smul, Complex.norm_natCast, mul_assoc]
      gcongr
      refine (hM x hx ξ r hr).trans_eq ?_
      push_cast
      ring_nf

@[simp]
theorem coefficient_resolvent (q : CoordinateSpace n × CoordinateSpace n) {r : ℂ} (hr : r ∈ R) :
    (resolvent p hp).coefficient q r = r • (1 - r • p.coefficient q).inverse :=
  indicator_of_mem (s := (R : Set ℂ)) hr fun r => r • (1 - r • p.coefficient q).inverse

/-- The resolvent is `r` times the normalized resolvent, at every reciprocal parameter `r`. -/
theorem coefficient_resolvent_eq_smul (q : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    (resolvent p hp).coefficient q r = r • (normalizedResolvent p hp).coefficient q r := by
  by_cases hr : r ∈ R
  · rw [coefficient_resolvent q hr, coefficient_normalizedResolvent q hr]
  · rw [(resolvent p hp).coefficient_of_notMem q r hr,
      (normalizedResolvent p hp).coefficient_of_notMem q r hr, smul_zero]

/-- The resolvent is a left inverse of `1 - r p(x, ξ)` up to the factor `r`:
`r (1 - r p)⁻¹ (1 - r p) = r` for `r ∈ R`. -/
theorem coefficient_resolvent_comp (q : CoordinateSpace n × CoordinateSpace n) {r : ℂ}
    (hr : r ∈ R) :
    (resolvent p hp).coefficient q r ∘L (1 - r • p.coefficient q) =
      r • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_resolvent_eq_smul, ContinuousLinearMap.smul_comp,
    coefficient_normalizedResolvent_comp q hr]

/-- The resolvent is a right inverse of `1 - r p(x, ξ)` up to the factor `r`:
`(1 - r p) r (1 - r p)⁻¹ = r` for `r ∈ R`. -/
theorem comp_coefficient_resolvent (q : CoordinateSpace n × CoordinateSpace n) {r : ℂ}
    (hr : r ∈ R) :
    (1 - r • p.coefficient q) ∘L (resolvent p hp).coefficient q r =
      r • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_resolvent_eq_smul, ContinuousLinearMap.comp_smul,
    comp_coefficient_normalizedResolvent q hr]

/-- The parameter derivatives of the resolvent:
`∂_r^(j + 1) (r (1 - r p(x, ξ))⁻¹) = (j + 1)! p(x, ξ) ^ j ((1 - r p(x, ξ))⁻¹) ^ (j + 2)`. -/
theorem iteratedDeriv_succ_coefficient_resolvent (j : ℕ)
    (q : CoordinateSpace n × CoordinateSpace n) {r : ℂ} (hr : r ∈ R) :
    iteratedDeriv (j + 1) ((resolvent p hp).coefficient q) r =
      ((j + 1)! : ℂ) • (p.coefficient q ^ j * (1 - r • p.coefficient q).inverse ^ (j + 2)) :=
  iteratedDeriv_succ_indicator_smul_inverse_one_sub_smul _ j hr (hp.isInvertible hr q)

/-- At the spectral parameter `λ ≠ 0` with `λ⁻¹ ∈ R`, the resolvent symbol is
`(λ - p(x, ξ))⁻¹`. -/
theorem coefficient_resolvent_inv (q : CoordinateSpace n × CoordinateSpace n) {μ : ℂ}
    (hμ : μ⁻¹ ∈ R) (hμ0 : μ ≠ 0) :
    (resolvent p hp).coefficient q μ⁻¹ = (μ • 1 - p.coefficient q).inverse := by
  have h : (p.coefficient q - μ • 1).inverse = -(μ • 1 - p.coefficient q).inverse := by
    rw [← neg_sub, ← neg_one_smul ℂ (μ • 1 - _), ContinuousLinearMap.inverse_smul]
    simp
  rw [coefficient_resolvent_eq_smul, coefficient_normalizedResolvent_inv q hμ hμ0, h]
  simp [smul_neg, smul_smul, hμ0]

end WeakParameterSymbol

/-! ### Scalar symbols and the Bessel weight -/

namespace Symbol

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **Scalar symbols are parameter-elliptic on sectors.** A symbol `p(x, ξ) = w(x, ξ) • id` of order
`d` with a nonnegative real weight `w` that is elliptic, `⟨ξ⟩ ^ d ≤ C w(x, ξ)` for positions in
each compact set, is parameter-elliptic on every set of reciprocal parameters in a sector
`Re r ≤ c ‖r‖` with `c < 1`: such a sector avoids the positive real axis, where the values
`r = 1 / λ` with `λ` in the spectrum lie. -/
theorem isParameterElliptic_of_coefficient_eq_smul {d : ℝ} {p : Symbol n V V d}
    {w : CoordinateSpace n × CoordinateSpace n → ℝ}
    (hpw : ∀ q, p.coefficient q = (w q : ℂ) • ContinuousLinearMap.id ℂ V) (hw : ∀ q, 0 ≤ w q)
    (hell : ∀ K : Set (CoordinateSpace n), IsCompact K →
      ∃ C, ∀ x ∈ K, ∀ ξ, (1 + ‖ξ‖ ^ 2) ^ (d / 2) ≤ C * w (x, ξ))
    {c : ℝ} (hc : c < 1) {R : Set ℂ} (hR : ∀ r ∈ R, r.re ≤ c * ‖r‖) :
    p.IsParameterElliptic R := by
  have hκ : 0 < (1 - max c (-1)) / 2 := by linarith [max_lt hc (show (-1 : ℝ) < 1 by norm_num)]
  refine fun K hK => ?_
  obtain ⟨C, hC⟩ := hell K hK
  refine ⟨max C 1 / ((1 - max c (-1)) / 2), fun x hx ξ r hr => ?_⟩
  set w₀ : ℝ := w (x, ξ)
  have hw₀ : 0 ≤ w₀ := hw (x, ξ)
  have hcoef : 1 - r • p.coefficient (x, ξ) = (1 - r * w₀) • ContinuousLinearMap.id ℂ V := by
    rw [hpw, smul_smul, sub_smul, one_smul, ContinuousLinearMap.one_def]
  have hlow := Complex.mul_one_add_le_norm_one_sub_mul (hR r hr) hw₀
  have hpos : 0 < ‖1 - r * w₀‖ := (mul_pos hκ (by positivity)).trans_le hlow
  rw [hcoef]
  refine ⟨(ContinuousLinearMap.isInvertible_smul_iff (norm_pos_iff.1 hpos)).2
    (by simpa using ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ V)),
    ?_⟩
  have hinv : ‖((1 - r * w₀) • ContinuousLinearMap.id ℂ V).inverse‖ ≤ ‖1 - r * w₀‖⁻¹ := by
    rw [ContinuousLinearMap.inverse_smul, ContinuousLinearMap.inverse_id, norm_smul, norm_inv]
    exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
  have hT := hC x hx ξ
  calc (1 + ‖r‖ * (1 + ‖ξ‖ ^ 2) ^ (d / 2)) * ‖((1 - r * w₀) • ContinuousLinearMap.id ℂ V).inverse‖
      ≤ (max C 1 * (1 + ‖r‖ * w₀)) * ‖1 - r * w₀‖⁻¹ := by
        gcongr
        nlinarith [norm_nonneg r, le_max_left C 1, le_max_right C 1,
          mul_le_mul_of_nonneg_left (hT.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) hw₀))
            (norm_nonneg r)]
    _ ≤ (max C 1 * (1 + ‖r‖ * w₀)) * ((1 - max c (-1)) / 2 * (1 + ‖r‖ * w₀))⁻¹ := by
        gcongr
    _ = max C 1 / ((1 - max c (-1)) / 2) := by
        field_simp

/-- **The Bessel weight is parameter-elliptic on sectors.** For every real `d`, the Bessel weight
`⟨ξ / 2π⟩ ^ d` of order `d` (`TauCeti.Symbol.besselPotential`), the symbol of
`(1 - Δ / 4π²) ^ (d / 2)`, is parameter-elliptic on every set of reciprocal parameters in a sector
`Re r ≤ c ‖r‖` with `c < 1`. -/
theorem isParameterElliptic_besselPotential (d : ℝ) {c : ℝ} (hc : c < 1)
    {R : Set ℂ} (hR : ∀ r ∈ R, r.re ≤ c * ‖r‖) :
    (besselPotential d : Symbol n V V d).IsParameterElliptic R :=
  isParameterElliptic_of_coefficient_eq_smul (coefficient_besselPotential d)
    (fun _ => by positivity)
    (fun _ _ => ⟨(2 * π) ^ |d|, fun _ _ ξ => one_add_norm_sq_rpow_le_of_norm_eq_mul
      (by linarith [Real.two_le_pi]) d (by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_inv_cancel_left₀ (by positivity)])⟩)
    hc hR

end Symbol

end TauCeti
