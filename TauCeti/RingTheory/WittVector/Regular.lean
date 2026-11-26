/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.WittVector.Complete
import TauCeti.RingTheory.WittVector.Teichmuller.Coeff

/-!
# Regular elements, regular pairs, and ideal intersections in Witt vectors

Let `S` be a perfect ring of characteristic `p` and `W(S) = WittVector p S` its ring of `p`-typical
Witt vectors. Since `W(S)` is `p`-torsion-free and `p`-adically separated with
`W(S) ⧸ (p) ≃+* S`, regularity of multiplication by `x : W(S)` and of the two-element sequence
`(p, x)` in either order is governed entirely by whether the zeroth Witt coordinate `x.coeff 0`
is a nonzerodivisor of `S`:

* `p` is a nonzerodivisor of `W(S)`.
* Multiplication by `x` on `W(S) ⧸ (p)` is regular iff `x.coeff 0 ∈ S⁰`.
* If `x.coeff 0 ∈ S⁰`, then `x ∈ (W(S))⁰`, multiplication by `p` is regular on `W(S) ⧸ (x)`, and
  both `[p, x]` and `[x, p]` are weakly regular sequences on `W(S)` (and regular when
  `¬ IsUnit (x.coeff 0)`).

Combining `p`-torsion-freeness of `W(S) ⧸ (x r)` with the `p`-adic Teichmüller expansion gives a
general lifting criterion for countable intersections of principal ideals: if `m ∈ (x r)` for all
`r ≥ 1`, each `(x r).coeff 0 ∈ S⁰`, and `⋂_{r ≥ 1} ((x r).coeff 0) = (m.coeff 0)` in `S`, then
`⋂_{r ≥ 1} (x r) = (m)` in `W(S)` (`WittVector.iInf_span_eq_span_of_coeff_zero`).

## Main results

* `WittVector.isSMulRegular_natCast`: `p` is `W(S)`-regular.
* `WittVector.mem_nonZeroDivisors_of_coeff_zero`: if `x.coeff 0 ∈ S⁰`, then `x ∈ (W(S))⁰`.
* `WittVector.isSMulRegular_quotient_natCast_of_coeff_zero`: if `x.coeff 0 ∈ S⁰`, then `p` is
  regular on `W(S) ⧸ (x)`.
* `WittVector.isWeaklyRegular_pair_natCast_of_coeff_zero` and
  `WittVector.isWeaklyRegular_pair_of_coeff_zero`: `[p, x]` and `[x, p]` are weakly regular.
* `WittVector.isRegular_pair_natCast_of_coeff_zero` and
  `WittVector.isRegular_pair_of_coeff_zero`: `[p, x]` and `[x, p]` are regular when additionally
  `¬ IsUnit (x.coeff 0)`.
* `WittVector.iInf_span_eq_span_of_coeff_zero`: lift a principal intersection of `(x r).coeff 0`
  from `S` to `W(S)`.
-/

public section

namespace WittVector

open Ideal RingTheory.Sequence
open scoped nonZeroDivisors

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

local notation "𝕎" => WittVector p

/-- Over a perfect ring of characteristic `p`, `p` is a regular element of `W(S)`. -/
theorem isSMulRegular_natCast : IsSMulRegular (𝕎 S) (p : 𝕎 S) :=
  IsSMulRegular.of_right_eq_zero_of_smul fun {_} h ↦
    eq_zero_of_p_mul_eq_zero _ (by simpa [smul_eq_mul, mul_comm] using h)

private noncomputable def quotSMulTopEquivQuotientSpan (x : 𝕎 S) :
    QuotSMulTop x (𝕎 S) ≃ₗ[𝕎 S] 𝕎 S ⧸ span {x} :=
  Submodule.quotEquivOfEq _ _ (by rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top])

/-- Multiplication by `x` on `W(S) ⧸ (p)` is regular iff `x.coeff 0` is a nonzerodivisor of `S`. -/
theorem isSMulRegular_quotientP_iff (x : 𝕎 S) :
    IsSMulRegular (𝕎 S ⧸ span {(p : 𝕎 S)}) x ↔ x.coeff 0 ∈ S⁰ := by
  let e : 𝕎 S ⧸ span {(p : 𝕎 S)} ≃+* S := quotientPEquiv
  have he (y : 𝕎 S ⧸ span {(p : 𝕎 S)}) : e (x • y) = x.coeff 0 * e y := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    rfl
  have hcongr : IsSMulRegular (𝕎 S ⧸ span {(p : 𝕎 S)}) x ↔ IsSMulRegular S (x.coeff 0) := by
    refine ⟨fun h y z hyz ↦ ?_, fun h y z hyz ↦ ?_⟩
    · obtain ⟨y, rfl⟩ := e.surjective y
      obtain ⟨z, rfl⟩ := e.surjective z
      exact congrArg e (h (e.injective (by simpa only [he, smul_eq_mul] using hyz)))
    · exact e.injective (h (by simpa only [← he, smul_eq_mul] using congrArg e hyz))
  exact hcongr.trans (isLeftRegular_iff.symm.trans
    ((Commute.isRegular_iff (Commute.all _)).symm.trans isRegular_iff_mem_nonZeroDivisors))

/-- Multiplication by `x` on `W(S) ⧸ p W(S)` is regular iff `x.coeff 0 ∈ S⁰`. -/
theorem isSMulRegular_quotSMulTop_natCast_iff (x : 𝕎 S) :
    IsSMulRegular (QuotSMulTop (p : 𝕎 S) (𝕎 S)) x ↔ x.coeff 0 ∈ S⁰ :=
  ((quotSMulTopEquivQuotientSpan (p : 𝕎 S)).isSMulRegular_congr x).trans
    (isSMulRegular_quotientP_iff x)

/-- If the zeroth Witt coordinate of `x` is a nonzerodivisor of `S`, then `x` is a nonzerodivisor
of `W(S)`. -/
theorem mem_nonZeroDivisors_of_coeff_zero {x : 𝕎 S} (hx : x.coeff 0 ∈ S⁰) : x ∈ (𝕎 S)⁰ := by
  refine mem_nonZeroDivisors_iff_right.mpr fun y hy ↦ ext fun n ↦ ?_
  -- Show `(p : 𝕎 S) ^ m ∣ y` for all `m` by induction, then take `m = n + 1`.
  have hdvd : ∀ m : ℕ, (p : 𝕎 S) ^ m ∣ y := by
    intro m
    induction m generalizing y with
    | zero => simp
    | succ m ih =>
      have hy0 : y.coeff 0 * x.coeff 0 = 0 := by
        simpa [mul_coeff_zero] using congrArg (coeff · 0) hy
      obtain ⟨y', rfl⟩ := mem_span_singleton.mp
        ((mem_span_p_iff_coeff_zero_eq_zero y).mpr (hx.2 _ hy0))
      have hy' : y' * x = 0 :=
        (mul_cancel_left_mem_nonZeroDivisors p_mem_nonZeroDivisors).mp (by linear_combination hy)
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih y' hy')
  rw [zero_coeff]
  exact (mem_span_p_pow_iff_le_coeff_eq_zero y (n + 1)).mp (mem_span_singleton.mpr (hdvd (n + 1)))
    n (Nat.lt_succ_self n)

/-- If `x.coeff 0 ∈ S⁰`, then `x` is `W(S)`-regular. -/
theorem isSMulRegular_of_coeff_zero {x : 𝕎 S} (hx : x.coeff 0 ∈ S⁰) : IsSMulRegular (𝕎 S) x :=
  ((Commute.isRegular_iff (Commute.all x)).mp
    (isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_coeff_zero hx))).isSMulRegular

/-- If `x.coeff 0 ∈ S⁰`, then `p` is regular on `W(S) ⧸ (x)`. -/
theorem isSMulRegular_quotient_natCast_of_coeff_zero {x : 𝕎 S} (hx : x.coeff 0 ∈ S⁰) :
    IsSMulRegular (𝕎 S ⧸ span {x}) (p : 𝕎 S) := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro y hy
  obtain ⟨z, hz⟩ := mem_span_singleton.mp hy
  have hz0 : z.coeff 0 * x.coeff 0 = 0 := by
    simpa [smul_eq_mul, mul_coeff_zero, coeff_p_zero, mul_comm] using congrArg (coeff · 0) hz.symm
  obtain ⟨z', rfl⟩ := mem_span_singleton.mp
    ((mem_span_p_iff_coeff_zero_eq_zero z).mpr (hx.2 _ hz0))
  refine mem_span_singleton.mpr ⟨z', (mul_cancel_left_mem_nonZeroDivisors
    p_mem_nonZeroDivisors).mp ?_⟩
  simpa [smul_eq_mul] using by linear_combination hz

/-- If `x.coeff 0 ∈ S⁰`, then `p` is regular on `W(S) ⧸ x W(S)`. -/
theorem isSMulRegular_quotSMulTop_natCast_of_coeff_zero {x : 𝕎 S} (hx : x.coeff 0 ∈ S⁰) :
    IsSMulRegular (QuotSMulTop x (𝕎 S)) (p : 𝕎 S) :=
  ((quotSMulTopEquivQuotientSpan x).isSMulRegular_congr (p : 𝕎 S)).mpr
    (isSMulRegular_quotient_natCast_of_coeff_zero hx)

/-- If `x.coeff 0 ∈ S⁰`, then `[p, x]` is a weakly regular sequence on `W(S)`. -/
theorem isWeaklyRegular_pair_natCast_of_coeff_zero {x : 𝕎 S} (hx : x.coeff 0 ∈ S⁰) :
    IsWeaklyRegular (𝕎 S) [(p : 𝕎 S), x] :=
  IsWeaklyRegular.cons isSMulRegular_natCast
    ((isWeaklyRegular_singleton_iff _ x).mpr ((isSMulRegular_quotSMulTop_natCast_iff x).mpr hx))

/-- If `x.coeff 0 ∈ S⁰`, then `[x, p]` is a weakly regular sequence on `W(S)`. -/
theorem isWeaklyRegular_pair_of_coeff_zero {x : 𝕎 S} (hx : x.coeff 0 ∈ S⁰) :
    IsWeaklyRegular (𝕎 S) [x, (p : 𝕎 S)] :=
  IsWeaklyRegular.cons (isSMulRegular_of_coeff_zero hx)
    ((isWeaklyRegular_singleton_iff _ (p : 𝕎 S)).mpr
      (isSMulRegular_quotSMulTop_natCast_of_coeff_zero hx))

/-- The ideal `(p, x)` of `W(S)` is proper iff `x.coeff 0` is not a unit of `S`. -/
theorem span_pair_natCast_ne_top_iff (x : 𝕎 S) :
    span {(p : 𝕎 S), x} ≠ ⊤ ↔ ¬ IsUnit (x.coeff 0) := by
  have hmap : (span {(p : 𝕎 S), x}).map constantCoeff = span {x.coeff 0} := by
    simp [Ideal.map_span]
  refine ⟨fun h hu ↦ h ?_, fun h htop ↦ h ?_⟩
  · have hx : (1 : 𝕎 S) - (x * teichmuller p hu.unit⁻¹.val) ∈ span {(p : 𝕎 S)} := by
      rw [mem_span_p_iff_coeff_zero_eq_zero, ← constantCoeff_apply, map_sub, map_one, map_mul,
        constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero, IsUnit.mul_val_inv,
        sub_self]
    rw [eq_top_iff_one]
    have hx' : (1 : 𝕎 S) - x * teichmuller p hu.unit⁻¹.val ∈ span {(p : 𝕎 S), x} :=
      Ideal.span_mono (by simp) hx
    have hmul : x * teichmuller p hu.unit⁻¹.val ∈ span {(p : 𝕎 S), x} :=
      Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    simpa using Ideal.add_mem _ hx' hmul
  · have : span {x.coeff 0} = ⊤ := by rw [← hmap, htop, Ideal.map_top]
    exact Ideal.span_singleton_eq_top.mp this

omit [CharP S p] [PerfectRing S p] in
private theorem isRegular_pair_iff_isWeaklyRegular_of_not_isUnit (a b : 𝕎 S)
    (h : span {a, b} ≠ ⊤) :
    IsRegular (𝕎 S) [a, b] ↔ IsWeaklyRegular (𝕎 S) [a, b] := by
  rw [isRegular_iff, Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq,
    smul_eq_mul, Ideal.mul_top, ← Ideal.span_insert, Set.insert_eq, Set.union_singleton,
    Set.pair_comm b a]
  exact and_iff_left h.symm

/-- If `x.coeff 0 ∈ S⁰` and `¬ IsUnit (x.coeff 0)`, then `[p, x]` is a regular sequence on `W(S)`.
-/
theorem isRegular_pair_natCast_of_coeff_zero {x : 𝕎 S} (hx : x.coeff 0 ∈ S⁰)
    (hnu : ¬ IsUnit (x.coeff 0)) : IsRegular (𝕎 S) [(p : 𝕎 S), x] :=
  (isRegular_pair_iff_isWeaklyRegular_of_not_isUnit _ _
    ((span_pair_natCast_ne_top_iff x).mpr hnu)).mpr
      (isWeaklyRegular_pair_natCast_of_coeff_zero hx)

/-- If `x.coeff 0 ∈ S⁰` and `¬ IsUnit (x.coeff 0)`, then `[x, p]` is a regular sequence on `W(S)`.
-/
theorem isRegular_pair_of_coeff_zero {x : 𝕎 S} (hx : x.coeff 0 ∈ S⁰)
    (hnu : ¬ IsUnit (x.coeff 0)) : IsRegular (𝕎 S) [x, (p : 𝕎 S)] :=
  (isRegular_pair_iff_isWeaklyRegular_of_not_isUnit x (p : 𝕎 S)
    (by rw [Set.pair_comm]; exact (span_pair_natCast_ne_top_iff x).mpr hnu)).mpr
      (isWeaklyRegular_pair_of_coeff_zero hx)

/-- The intersection of all `(p ^ r)` for `r ≥ 1` in `W(S)` is zero. -/
theorem iInf_span_natCast_pow_eq_bot :
    (⨅ (r : ℕ) (_ : 1 ≤ r), span {(p : 𝕎 S) ^ r}) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  ext n
  rw [zero_coeff]
  rw [Submodule.mem_iInf] at hx
  have hx' := (Submodule.mem_iInf _).mp (hx (n + 1)) (Nat.le_add_left 1 n)
  exact (mem_span_p_pow_iff_le_coeff_eq_zero x (n + 1)).mp hx' n (Nat.lt_succ_self n)

private theorem exists_sub_teichmuller_eq_natCast_mul {x : ℕ → 𝕎 S} {m : 𝕎 S}
    (hm : ∀ r, 1 ≤ r → m ∈ span {x r}) (hx₀ : ∀ r, 1 ≤ r → (x r).coeff 0 ∈ S⁰)
    (hinf : (⨅ (r : ℕ) (_ : 1 ≤ r), span {(x r).coeff 0}) = span {m.coeff 0})
    (w : {w : 𝕎 S // w ∈ ⨅ (r : ℕ) (_ : 1 ≤ r), span {x r}}) :
    ∃ a : S, ∃ w' : {w' : 𝕎 S // w' ∈ ⨅ (r : ℕ) (_ : 1 ≤ r), span {x r}},
      w.val - m * teichmuller p a = p * w'.val := by
  let I : Ideal (𝕎 S) := ⨅ (r : ℕ) (_ : 1 ≤ r), span {x r}
  have hmI : m ∈ I := (Submodule.mem_iInf _).mpr fun r ↦ (Submodule.mem_iInf _).mpr fun hr ↦ hm r hr
  have hw₀ : w.val.coeff 0 ∈ span {m.coeff 0} := by
    rw [← hinf, Submodule.mem_iInf]
    intro r
    rw [Submodule.mem_iInf]
    intro hr
    have hwr := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp w.property r) hr
    obtain ⟨c, hc⟩ := mem_span_singleton.mp hwr
    exact mem_span_singleton.mpr
      ⟨c.coeff 0, by simpa [mul_coeff_zero] using congrArg (coeff · 0) hc⟩
  obtain ⟨a, ha⟩ := mem_span_singleton.mp hw₀
  have hsub : w.val - m * teichmuller p a ∈ I := I.sub_mem w.property (I.mul_mem_right _ hmI)
  have hcoeff : (w.val - m * teichmuller p a).coeff 0 = 0 := by
    rw [← constantCoeff_apply, map_sub, map_mul, constantCoeff_apply, constantCoeff_apply,
      constantCoeff_apply, teichmuller_coeff_zero, ha, sub_self]
  obtain ⟨w', hw'⟩ := mem_span_singleton.mp ((mem_span_p_iff_coeff_zero_eq_zero _).mpr hcoeff)
  have hw'I : w' ∈ I := by
    rw [Submodule.mem_iInf]
    intro r
    rw [Submodule.mem_iInf]
    intro hr
    have hreg := isSMulRegular_quotient_natCast_of_coeff_zero (hx₀ r hr)
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hreg
    have hsubr := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hsub r) hr
    exact hreg w' (by simpa [smul_eq_mul, ← hw'] using hsubr)
  exact ⟨a, ⟨w', hw'I⟩, hw'⟩

/-- **Lifting a principal intersection of ideals from `S` to `W(S)`.** If `m ∈ (x r)` for all
`r ≥ 1`, each `(x r).coeff 0` is a nonzerodivisor of `S`, and `⋂_{r ≥ 1} ((x r).coeff 0) = (m₀)`
in `S`, then `⋂_{r ≥ 1} (x r) = (m)` in `W(S)`. Each element `z` of the intersection is expanded
`p`-adically as `m * ∑ [aₙ] pⁿ` using `p`-torsion-freeness of `W(S) ⧸ (x r)`. -/
theorem iInf_span_eq_span_of_coeff_zero {x : ℕ → 𝕎 S} {m : 𝕎 S}
    (hm : ∀ r, 1 ≤ r → m ∈ span {x r}) (hx₀ : ∀ r, 1 ≤ r → (x r).coeff 0 ∈ S⁰)
    (hinf : (⨅ (r : ℕ) (_ : 1 ≤ r), span {(x r).coeff 0}) = span {m.coeff 0}) :
    (⨅ (r : ℕ) (_ : 1 ≤ r), span {x r}) = span {m} := by
  refine le_antisymm ?_
    (le_iInf fun r ↦ le_iInf fun hr ↦ Ideal.span_le.mpr (by simpa using hm r hr))
  choose aSeq next hnext using exists_sub_teichmuller_eq_natCast_mul hm hx₀ hinf
  intro z hz
  let I : Ideal (𝕎 S) := ⨅ (r : ℕ) (_ : 1 ≤ r), span {x r}
  let wSeq : ℕ → {w : 𝕎 S // w ∈ I} := Nat.rec ⟨z, hz⟩ fun _ w ↦ next w
  let y : 𝕎 S := mk p fun n ↦ aSeq (wSeq n) ^ p ^ n
  have hsum (n : ℕ) :
      z - m * ∑ i ∈ Finset.range n, teichmuller p (aSeq (wSeq i)) * (p : 𝕎 S) ^ i =
        (p : 𝕎 S) ^ n * (wSeq n).val := by
    induction n with
    | zero => simp [wSeq]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ← sub_sub, ih]
      have hn := hnext (wSeq n)
      dsimp only [wSeq]
      rw [pow_succ']
      linear_combination (p : 𝕎 S) ^ n * hn
  have hyCoeff (i : ℕ) : y.teichmullerCoeff i = aSeq (wSeq i) :=
    teichmullerCoeff_eq_iff.mpr (congrFun (coeff_mk p _) i)
  have hy (n : ℕ) : (p : 𝕎 S) ^ (n + 1) ∣ y -
      ∑ i ∈ Finset.range (n + 1), teichmuller p (aSeq (wSeq i)) * (p : 𝕎 S) ^ i := by
    rw [Nat.range_succ_eq_Iic]
    simpa [hyCoeff] using pow_dvd_sub_sum_teichmullerCoeff y n
  have hdvd (n : ℕ) : (p : 𝕎 S) ^ (n + 1) ∣ z - m * y := by
    have h1 : (p : 𝕎 S) ^ (n + 1) ∣
        z - m * ∑ i ∈ Finset.range (n + 1), teichmuller p (aSeq (wSeq i)) * (p : 𝕎 S) ^ i :=
      ⟨(wSeq (n + 1)).val, hsum (n + 1)⟩
    convert dvd_sub h1 ((hy n).mul_left m) using 1
    ring
  refine mem_span_singleton.mpr ⟨y, sub_eq_zero.mp (ext fun n ↦ ?_)⟩
  rw [zero_coeff]
  exact (mem_span_p_pow_iff_le_coeff_eq_zero (z - m * y) (n + 1)).mp
    (mem_span_singleton.mpr (hdvd n)) n (Nat.lt_succ_self n)

end WittVector
