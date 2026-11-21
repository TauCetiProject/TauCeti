/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.IteratedDeriv.Indicator
import TauCeti.Analysis.Calculus.IteratedFDeriv.ContinuousLinearMapInverse
import TauCeti.Analysis.Complex.SectorBounds
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The normalized resolvent of a parameter-elliptic symbol

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
* `TauCeti.Symbol.isParameterElliptic_besselPotential`: the Bessel weight `⟨ξ / 2π⟩ ^ d` of every
  real order `d` (`TauCeti.Symbol.besselPotential`) is parameter-elliptic on every sector
  `Re r ≤ c ‖r‖` with `c < 1`, so that the normalized resolvent of the Bessel potential
  `(1 - Δ / 4π²) ^ (d / 2)` is a weakly parameter-dependent symbol.

## Implementation notes

The estimates are proved at one point `(x, ξ)` at a time, after dilating the frequency by
`t = ⟨ξ⟩`. The derivatives at `(0, 0)` of `(y, v) ↦ 1 - r p(x + y, ξ + t v)` are of the size
`s = 1 + ‖r‖ ⟨ξ⟩ ^ d` of the function itself, because each frequency derivative of `p` gains a
factor `⟨ξ⟩⁻¹` which the dilation compensates (`TauCeti.mixedDeriv_comp_add_smul`). By
parameter-ellipticity its inverse at `(0, 0)` has size `1 / s`, so the derivatives of the inverse
have size `1 / s ≤ 1` there (`TauCeti.exists_norm_iteratedFDeriv_clm_inverse_le`), with constants
independent of `r`, `x` and `ξ`. Undoing the dilation gives the symbol estimates of order `0`, and
the Leibniz rule those of the parameter derivatives `j! p ^ j ((1 - r p)⁻¹) ^ (j + 1)`, of order
`d j`.

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

/-! ### Frequency dilations of mixed derivatives -/

section Dilation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- **Mixed derivatives under a frequency dilation.** Dilating the frequency by `t` about `ξ`
multiplies a mixed derivative by `t` for each frequency direction: the mixed derivative
`∂_y^α ∂_v^β` at `(0, 0)` of `(y, v) ↦ a(x + y, ξ + t v)` is `t ^ |β|` times
`∂_x^α ∂_ξ^β a(x, ξ)`. -/
theorem mixedDeriv_comp_add_smul {a : CoordinateSpace n × CoordinateSpace n → A}
    {α β : List (Fin n)} (ha : ContDiff ℝ (α.length + β.length) a) (x ξ : CoordinateSpace n)
    (t : ℝ) :
    mixedDeriv α β (fun q => a (x + q.1, ξ + t • q.2)) 0 0 =
      t ^ β.length • mixedDeriv α β a x ξ := by
  have h : (fun q : CoordinateSpace n × CoordinateSpace n => a (x + q.1, ξ + t • q.2)) =
      (fun q => a ((x, ξ) + q)) ∘ (ContinuousLinearMap.id ℝ (CoordinateSpace n)).prodMap
        (t • ContinuousLinearMap.id ℝ (CoordinateSpace n)) := by
    funext q
    rfl
  rw [h, mixedDeriv_comp_prodMap (a := fun q => a ((x, ξ) + q)) _ _
      (ha.comp (contDiff_const.add contDiff_id)) 0 0,
    mixedDeriv_eq_iteratedFDeriv_append α β ha x ξ, iteratedFDeriv_comp_add_left]
  have hv : (Fin.append (fun i => ((ContinuousLinearMap.id ℝ (CoordinateSpace n))
        (EuclideanSpace.single (α.get i) 1), (0 : CoordinateSpace n)))
      fun i => ((0 : CoordinateSpace n), (t • ContinuousLinearMap.id ℝ (CoordinateSpace n))
        (EuclideanSpace.single (β.get i) 1))) =
      fun i => (Fin.append (fun _ => (1 : ℝ)) fun _ => t) i •
        Fin.append (fun i => (EuclideanSpace.single (α.get i) 1, (0 : CoordinateSpace n)))
          (fun i => ((0 : CoordinateSpace n), EuclideanSpace.single (β.get i) 1)) i := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  have hprod : ∏ i, (Fin.append (fun _ : Fin α.length => (1 : ℝ))
      fun _ : Fin β.length => t) i = t ^ β.length := by
    simp [Fin.prod_univ_add]
  simp only [ContinuousLinearMap.coe_id', id_eq, map_zero, Prod.mk_zero_zero, add_zero] at hv ⊢
  rw [hv, ContinuousMultilinearMap.map_smul_univ, hprod]

end Dilation

/-! ### Bounds for products at a point -/

section Leibniz

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℂ V]

/-- If the derivatives of order at most `k` of `f` and `g` at `y` are bounded by `a` and `b`,
those of `f g` are bounded by `2 ^ k a b`. -/
private theorem norm_iteratedFDeriv_mul_le_of_forall_le {f g : E → V →L[ℂ] V} {k : ℕ}
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) {y : E} {a b : ℝ}
    (ha : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f y‖ ≤ a) (hb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g y‖ ≤ b) :
    ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun z => f z * g z) y‖ ≤ 2 ^ k * a * b := by
  intro i hi
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 (Nat.zero_le _))
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  calc ‖iteratedFDeriv ℝ i (fun z => f z * g z) y‖
      ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l f y‖ *
          ‖iteratedFDeriv ℝ (i - l) g y‖ :=
        norm_iteratedFDeriv_mul_le hf hg y (by exact_mod_cast hi)
    _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * a * b := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hl' : l ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
        gcongr
        · exact ha l (hl'.trans hi)
        · exact hb (i - l) ((Nat.sub_le i l).trans hi)
    _ = 2 ^ i * a * b := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ) * a * b) (Nat.sum_range_choose i)
    _ ≤ 2 ^ k * a * b := by
        gcongr
        · norm_num

/-- If the derivatives of order at most `k` of `f` at `y` are bounded by `a`, those of `f ^ j`
are bounded by `(2 ^ k a) ^ j`. -/
private theorem norm_iteratedFDeriv_pow_le_of_forall_le {f : E → V →L[ℂ] V} {k : ℕ}
    (hf : ContDiff ℝ ∞ f) {y : E} {a : ℝ} (ha : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f y‖ ≤ a) (j : ℕ) :
    ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun z => f z ^ j) y‖ ≤ (2 ^ k * a) ^ j := by
  induction j with
  | zero =>
    intro i _
    simp only [pow_zero]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [norm_iteratedFDeriv_zero]
      exact ContinuousLinearMap.norm_id_le
    · simp [iteratedFDeriv_const_of_ne hi]
  | succ j ih =>
    intro i hi
    have h := norm_iteratedFDeriv_mul_le_of_forall_le ((hf.pow j).of_le (by exact_mod_cast le_top))
      (hf.of_le (by exact_mod_cast le_top)) ih ha i hi
    simp only [pow_succ] at h ⊢
    linarith

end Leibniz

/-! ### Parameter derivatives of `(1 - r P)⁻¹` -/

section ParameterDeriv

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
private theorem commute_ringInverse_one_sub_smul (P : 𝔸) (r : ℂ) :
    Commute P (Ring.inverse (1 - r • P)) := by
  by_cases hr : IsUnit (1 - r • P)
  · obtain ⟨u, hu⟩ := hr
    have hc : Commute P (u : 𝔸) :=
      hu ▸ (Commute.one_right P).sub_right ((Commute.refl P).smul_right r)
    rw [← hu, Ring.inverse_unit]
    exact hc.units_inv_right
  · rw [Ring.inverse_non_unit _ hr]
    exact Commute.zero_right P

/-- `∂_r^j (1 - r P)⁻¹ = j! P ^ j ((1 - r P)⁻¹) ^ (j + 1)` where `1 - r P` is invertible: the
commutative form of `TauCeti.iteratedDeriv_ringInverse_add_smul`, as `P` commutes with
`(1 - r P)⁻¹`. -/
private theorem iteratedDeriv_ringInverse_one_sub_smul (P : 𝔸) (j : ℕ) {r : ℂ}
    (hr : IsUnit (1 - r • P)) :
    iteratedDeriv j (fun s : ℂ => Ring.inverse (1 - s • P)) r =
      (j ! : ℂ) • (P ^ j * Ring.inverse (1 - r • P) ^ (j + 1)) := by
  have h1 (s : ℂ) : 1 - s • P = 1 + s • -P := by rw [smul_neg, sub_eq_add_neg]
  have hc := commute_ringInverse_one_sub_smul P r
  simp only [h1] at hr hc ⊢
  have hI : Ring.inverse (1 + r • -P) * (P * Ring.inverse (1 + r • -P)) ^ j =
      P ^ j * Ring.inverse (1 + r • -P) ^ (j + 1) := by
    rw [hc.mul_pow, ← mul_assoc, ← (hc.pow_left j).eq, mul_assoc, ← pow_succ']
  rw [iteratedDeriv_ringInverse_add_smul 1 (-P) j hr, neg_mul, ← hI]
  rcases Nat.even_or_odd j with h | h <;> simp [h.neg_one_pow, h.neg_pow]

end ParameterDeriv

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

/-- With `t = ⟨ξ⟩`, `t ^ i * (1 + ‖ξ‖²) ^ ((d - i) / 2) = (1 + ‖ξ‖²) ^ (d / 2)`. -/
private theorem japaneseBracket_pow_mul_rpow (ξ : CoordinateSpace n) (i : ℕ) (d : ℝ) :
    ((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ i * (1 + ‖ξ‖ ^ 2) ^ ((d - i) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ (d / 2) := by
  have hu : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le, ← Real.rpow_add hu]
  congr 1
  ring

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
    p.contDiff_coefficient.comp ((contDiff_const.add contDiff_fst).prodMk
      (contDiff_const.add (contDiff_snd.const_smul t)))
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
  have hone : ‖iteratedFDeriv ℝ i (fun _ : E => (1 : V →L[ℂ] V)) y‖ ≤ 1 := by
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [norm_iteratedFDeriv_zero]
      exact ContinuousLinearMap.norm_id_le
    · simp [iteratedFDeriv_const_of_ne hi0]
  rw [hsub]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul]
  have : ‖r‖ * ‖iteratedFDeriv ℝ i P y‖ ≤ ‖r‖ * (S * T) := by gcongr; exact hPb i hi
  nlinarith [norm_nonneg r, mul_nonneg (norm_nonneg r) hT]

/-- **Dilated estimates for the inverse.** With `t = ⟨ξ⟩`, the derivatives of order at most `k`
at `(0, 0)` of `(y, v) ↦ (1 - r p(x + y, ξ + t v))⁻¹` are bounded uniformly for `x ∈ K`, all `ξ`
and `r ∈ R`: by parameter-ellipticity the inverse at `(0, 0)` is of size `1 / s` for the size
`s = 1 + ‖r‖ ⟨ξ⟩ ^ d` of the derivatives of `1 - r p` there. -/
private theorem exists_norm_iteratedFDeriv_dilate_inverse_le (hp : p.IsParameterElliptic R)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ c, 0 ≤ c ∧ ∀ x ∈ K, ∀ ξ, ∀ r ∈ R, ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (fun q : CoordinateSpace n × CoordinateSpace n =>
          (1 - r • p.coefficient (x + q.1, ξ + (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) • q.2)).inverse) 0‖ ≤
        c := by
  obtain ⟨S, hS0, hS⟩ := exists_norm_iteratedFDeriv_dilate_le p hK k
  obtain ⟨B, hB⟩ := hp K hK
  obtain ⟨c, hc⟩ := exists_norm_iteratedFDeriv_clm_inverse_le
    (E := CoordinateSpace n × CoordinateSpace n) (V := V) (W := V) k (1 + S) B
  refine ⟨|c|, abs_nonneg c, fun x hx ξ r hr i hi => ?_⟩
  set T : ℝ := (1 + ‖ξ‖ ^ 2) ^ (d / 2)
  set s : ℝ := 1 + ‖r‖ * T
  have hs : 1 ≤ s := le_add_of_nonneg_right (by positivity)
  set t : ℝ := (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)
  set P : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] V :=
    fun q => p.coefficient (x + q.1, ξ + t • q.2)
  have hP : ContDiff ℝ ∞ P := p.contDiff_coefficient.comp ((contDiff_const.add contDiff_fst).prodMk
    (contDiff_const.add (contDiff_snd.const_smul t)))
  have hF0 : 1 - r • P 0 = 1 - r • p.coefficient (x, ξ) := by simp [P]
  have hFinvb : ‖(1 - r • P 0).inverse‖ ≤ B / s := by
    rw [le_div_iff₀ (by positivity), mul_comm, hF0]
    exact (hB x hx ξ r hr).2
  have h := hc (fun q => 1 - r • P q) univ 0 s (by positivity) isOpen_univ (mem_univ _)
    (contDiff_const.sub (hP.const_smul r)).contDiffOn (fun q _ => hp.isInvertible hr _)
    (norm_iteratedFDeriv_one_sub_smul_le hP hS0 (by positivity) (hS x hx ξ) r) hFinvb i hi
  exact h.trans ((div_le_div_of_nonneg_right (le_abs_self c) (by positivity)).trans
    (div_le_self (abs_nonneg c) hs))

/-- **Symbol estimates for the parameter derivatives, uniformly in the parameter.** For a
parameter-elliptic symbol `p` of order `d`, the functions
`(x, ξ) ↦ p(x, ξ) ^ j ((1 - r p(x, ξ))⁻¹) ^ (j + 1)` satisfy the symbol estimates of order `d j`
on every compact set of positions, uniformly in `r ∈ R`. -/
private theorem exists_norm_mixedDeriv_pow_mul_inverse_pow_le (hp : p.IsParameterElliptic R)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (j : ℕ) (α β : List (Fin n)) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ K, ∀ ξ, ∀ r ∈ R,
      ‖mixedDeriv α β (fun q => p.coefficient q ^ j * (1 - r • p.coefficient q).inverse ^ (j + 1))
          x ξ‖ ≤ M * (1 + ‖ξ‖ ^ 2) ^ ((d * j - β.length) / 2) := by
  set k := α.length + β.length
  obtain ⟨S, hS0, hS⟩ := exists_norm_iteratedFDeriv_dilate_le p hK k
  obtain ⟨c, hc0, hc⟩ := exists_norm_iteratedFDeriv_dilate_inverse_le hp hK k
  set M := (2 : ℝ) ^ k * (2 ^ k * S) ^ j * (2 ^ k * c) ^ (j + 1)
  refine ⟨M, by positivity, fun x hx ξ r hr => ?_⟩
  set u : ℝ := 1 + ‖ξ‖ ^ 2
  have hu : 0 < u := by positivity
  set t : ℝ := u ^ ((1 : ℝ) / 2)
  have ht : 0 < t := Real.rpow_pos_of_pos hu _
  set g : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] V :=
    fun q => p.coefficient q ^ j * (1 - r • p.coefficient q).inverse ^ (j + 1)
  have hinv : ContDiff ℝ ∞ fun q => (1 - r • p.coefficient q).inverse :=
    (contDiff_const.sub (p.contDiff_coefficient.const_smul r)).clm_inverse
      fun q => hp.isInvertible hr q
  have hg : ContDiff ℝ ∞ g := (p.contDiff_coefficient.pow j).mul (hinv.pow (j + 1))
  -- The dilation of `g` is a product of the dilations of `p` and of the inverse, whose derivatives
  -- at `0` are of size `⟨ξ⟩ ^ d` and `1`; by the Leibniz rule its derivatives are of size
  -- `⟨ξ⟩ ^ (d j)`.
  have hD : ContDiff ℝ ∞ fun q : CoordinateSpace n × CoordinateSpace n =>
      (x + q.1, ξ + t • q.2) :=
    (contDiff_const.add contDiff_fst).prodMk (contDiff_const.add (contDiff_snd.const_smul t))
  have hP := p.contDiff_coefficient.comp hD
  have hG := hinv.comp hD
  have hprod := norm_iteratedFDeriv_mul_le_of_forall_le
    ((hP.pow j).of_le (by exact_mod_cast le_top))
    ((hG.pow (j + 1)).of_le (by exact_mod_cast le_top))
    (norm_iteratedFDeriv_pow_le_of_forall_le hP (hS x hx ξ) j)
    (norm_iteratedFDeriv_pow_le_of_forall_le hG (hc x hx ξ r hr) (j + 1)) k le_rfl
  -- Undo the dilation: each frequency derivative costs a factor `t = ⟨ξ⟩`.
  have hkey : t ^ β.length * ‖mixedDeriv α β g x ξ‖ ≤ M * (u ^ (d / 2)) ^ j := by
    have h1 := norm_mixedDeriv_le α β ((hg.comp hD).of_le (by exact_mod_cast le_top)) 0 0
    simp only [Function.comp_def] at h1
    rw [mixedDeriv_comp_add_smul (hg.of_le (by exact_mod_cast le_top)), norm_smul,
      Real.norm_eq_abs, abs_pow, abs_of_pos ht, Prod.mk_zero_zero] at h1
    refine h1.trans (hprod.trans_eq ?_)
    simp only [M]
    ring
  have hTj : (u ^ (d / 2)) ^ j = u ^ ((d * j - β.length) / 2) * t ^ β.length := by
    simp only [t]
    rw [← Real.rpow_natCast (u ^ (d / 2)) j, ← Real.rpow_mul hu.le,
      ← Real.rpow_natCast (u ^ ((1 : ℝ) / 2)) β.length, ← Real.rpow_mul hu.le,
      ← Real.rpow_add hu]
    congr 1
    ring
  rw [hTj] at hkey
  exact le_of_mul_le_mul_left (hkey.trans_eq (by ring)) (pow_pos ht _)

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
    exact ((p.contDiff_coefficient.pow j).mul (((contDiff_const.sub
      (p.contDiff_coefficient.const_smul r)).clm_inverse fun q => hp.isInvertible hr q).pow
        (j + 1))).const_smul _
  exists_bound K hK j α β := by
    obtain ⟨M, hM0, hM⟩ := exists_norm_mixedDeriv_pow_mul_inverse_pow_le hp hK j α β
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
    rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hμ0, neg_smul, neg_smul, one_smul,
      sub_neg_eq_add, neg_add_eq_sub]
  rw [coefficient_normalizedResolvent q hμ, h, ContinuousLinearMap.inverse_smul, inv_neg, inv_inv]

end WeakParameterSymbol

/-! ### The Bessel weight -/

namespace Symbol

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- `⟨ξ⟩ ^ d ≤ (2π) ^ |d| ⟨ξ / 2π⟩ ^ d`. -/
private theorem rpow_le_two_pi_rpow_abs_mul_rpow (d : ℝ) (ξ : CoordinateSpace n) :
    (1 + ‖ξ‖ ^ 2) ^ (d / 2) ≤ (2 * π) ^ |d| * (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (d / 2) := by
  have hπ : 0 < 2 * π := by positivity
  have hπ1 : 1 ≤ 2 * π := by linarith [Real.two_le_pi]
  have hnorm : ‖(2 * π)⁻¹ • ξ‖ = (2 * π)⁻¹ * ‖ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rcases le_total 0 d with hd | hd
  · have hbase : (2 * π)⁻¹ ^ 2 * (1 + ‖ξ‖ ^ 2) ≤ 1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2 := by
      have h1 : (2 * π)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hπ1)
      rw [hnorm, mul_pow]
      nlinarith
    have hle := Real.rpow_le_rpow (by positivity) hbase (by positivity : 0 ≤ d / 2)
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), Real.inv_rpow hπ.le] at hle
    rw [show (((2 : ℕ) : ℝ) * (d / 2)) = d by push_cast; ring] at hle
    rw [abs_of_nonneg hd, ← inv_mul_le_iff₀ (Real.rpow_pos_of_pos hπ d)]
    exact hle
  · have hbase : 1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 2 := by
      have h1 : (2 * π)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hπ1
      rw [hnorm]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg ξ) h1
    exact (Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)).trans
      (le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hπ1 (abs_nonneg d)))

/-- **The Bessel weight is parameter-elliptic on sectors.** For every real `d`, the Bessel weight
`⟨ξ / 2π⟩ ^ d` of order `d` (`TauCeti.Symbol.besselPotential`), the symbol of
`(1 - Δ / 4π²) ^ (d / 2)`, is parameter-elliptic on every set of reciprocal parameters in a sector
`Re r ≤ c ‖r‖` with `c < 1`: such a sector avoids the positive real axis, where the values
`r = 1 / λ` with `λ` in the spectrum lie. -/
theorem isParameterElliptic_besselPotential (d : ℝ) {c : ℝ} (hc : c < 1)
    {R : Set ℂ} (hR : ∀ r ∈ R, r.re ≤ c * ‖r‖) :
    (besselPotential d : Symbol n V V d).IsParameterElliptic R := by
  have hκ : 0 < (1 - max c (-1)) / 2 := by linarith [max_lt hc (show (-1 : ℝ) < 1 by norm_num)]
  refine fun K _ => ⟨(2 * π) ^ |d| / ((1 - max c (-1)) / 2), fun x _ ξ r hr => ?_⟩
  set w : ℝ := (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (d / 2)
  have hw : 0 ≤ w := by positivity
  have hcoef : 1 - r • (besselPotential d : Symbol n V V d).coefficient (x, ξ) =
      (1 - r * w) • ContinuousLinearMap.id ℂ V := by
    rw [coefficient_besselPotential, smul_smul, sub_smul, one_smul]
    rfl
  have hlow : (1 - max c (-1)) / 2 * (1 + ‖r‖ * w) ≤ ‖1 - r * w‖ := by
    have hnorm : ‖r * (w : ℂ)‖ = ‖r‖ * w := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    have h := Complex.mul_add_norm_le_norm_ofReal_sub (z := r * w) (c := c) zero_le_one (by
      rw [hnorm, Complex.re_mul_ofReal]
      nlinarith [mul_le_mul_of_nonneg_right (hR r hr) hw])
    rwa [hnorm, Complex.ofReal_one] at h
  have hpos : 0 < ‖1 - r * w‖ := (mul_pos hκ (by positivity)).trans_le hlow
  rw [hcoef]
  refine ⟨(ContinuousLinearMap.isInvertible_smul_iff (norm_pos_iff.1 hpos)).2
    (by simpa using ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ V)),
    ?_⟩
  have hinv : ‖((1 - r * w) • ContinuousLinearMap.id ℂ V).inverse‖ ≤ ‖1 - r * w‖⁻¹ := by
    rw [ContinuousLinearMap.inverse_smul, ContinuousLinearMap.inverse_id, norm_smul, norm_inv]
    exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le
  have hT := rpow_le_two_pi_rpow_abs_mul_rpow d ξ
  have h2π : 1 ≤ (2 * π) ^ |d| := Real.one_le_rpow (by linarith [Real.two_le_pi]) (abs_nonneg d)
  calc (1 + ‖r‖ * (1 + ‖ξ‖ ^ 2) ^ (d / 2)) * ‖((1 - r * w) • ContinuousLinearMap.id ℂ V).inverse‖
      ≤ ((2 * π) ^ |d| * (1 + ‖r‖ * w)) * ‖1 - r * w‖⁻¹ := by
        gcongr
        nlinarith [norm_nonneg r, mul_le_mul_of_nonneg_left hT (norm_nonneg r)]
    _ ≤ ((2 * π) ^ |d| * (1 + ‖r‖ * w)) * ((1 - max c (-1)) / 2 * (1 + ‖r‖ * w))⁻¹ := by
        gcongr
    _ = (2 * π) ^ |d| / ((1 - max c (-1)) / 2) := by
        field_simp

end Symbol

end TauCeti
