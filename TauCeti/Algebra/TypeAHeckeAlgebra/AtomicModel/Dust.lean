/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.CycleWord
public import TauCeti.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import TauCeti.Analysis.Normed.Ring.InfiniteSum

/-!
# The continuous-dust limit for cycle-trace generating functions

Splitting weight `γ` across `N` positive (`b = true`) or negative (`b = false`) letters of weight
`γ / N` yields `exp (((q : 𝕜) ^ 2 - 1) * γ * x)` as `N → ∞`. We prove coefficientwise limits over
`[RCLike 𝕜]` and complex generating-function convergence (cf. Neretin, arXiv:2101.02133,
§§1.6–1.7, §3.1).
-/

public section

open Filter
open scoped Nat Topology

namespace TauCeti.TypeAHeckeAlgebra

/-- Sign predicate on `ι ⊕ₗ Fin N`, extending `pos : ι → Prop` by `N` dust letters of sign `b`. -/
def dustPos {ι : Type*} (pos : ι → Prop) (b : Bool) (N : ℕ) (a : ι ⊕ₗ Fin N) : Prop :=
  Sum.elim pos (fun _ ↦ b = true) (ofLex a)

instance {ι : Type*} (pos : ι → Prop) [DecidablePred pos] (b : Bool) (N : ℕ) :
    DecidablePred (dustPos pos b N) := fun a ↦
  match ha : ofLex a with
  | Sum.inl i => decidable_of_iff (pos i) (by simp [dustPos, ha])
  | Sum.inr _ => decidable_of_iff (b = true) (by simp [dustPos, ha])

/-- Evaluating `dustPos` on the background summand recovers `pos`. -/
@[simp] theorem dustPos_inl {ι : Type*} (pos : ι → Prop) (b : Bool) (N : ℕ) (i : ι) :
    dustPos pos b N (Sum.inlₗ i) ↔ pos i := Iff.rfl

/-- Evaluating `dustPos` on the dust summand recovers `b = true`. -/
@[simp] theorem dustPos_inr {ι : Type*} (pos : ι → Prop) (b : Bool) (N : ℕ) (k : Fin N) :
    dustPos pos b N (Sum.inrₗ k) ↔ b = true := Iff.rfl

private theorem tendsto_inv_natCast_zero {𝕜 : Type*} [RCLike 𝕜] :
    Tendsto (fun N : ℕ ↦ ((N : 𝕜)⁻¹)) atTop (𝓝 0) := by
  simpa [Function.comp_def, map_inv₀, RCLike.ofReal_natCast] using
    ((RCLike.continuous_ofReal (K := 𝕜)).tendsto 0).comp
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)

private theorem atomicTrace_orderIso {R α β : Type*} [CommRing R] [LinearOrder α] [LinearOrder β]
    [Finite α] [Finite β] (posα : α → Prop) (posβ : β → Prop) [DecidablePred posα]
    [DecidablePred posβ] (q : Rˣ) (pα : α → R) (pβ : β → R) (e : α ≃o β)
    (hpos : ∀ a, posβ (e a) ↔ posα a) (hp : ∀ a, pβ (e a) = pα a) (n : ℕ)
    (x : TypeAHeckeAlgebra R q n) : atomicTrace posα q pα n x = atomicTrace posβ q pβ n x := by
  let := Fintype.ofFinite α; let := Fintype.ofFinite β
  rw [atomicTrace_eq_sum, atomicTrace_eq_sum, ← (Equiv.piCongrRight fun _ ↦ e.toEquiv).sum_comp]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [show (Equiv.piCongrRight fun _ ↦ e.toEquiv) w = e ∘ w from rfl,
    signedChecked_strictMono_single_apply posβ q posα e.strictMono hpos x w w]; simp [hp]

private theorem tendsto_coeff_one_add_div_pow {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) (k : ℕ) :
    Tendsto (fun N : ℕ ↦ PowerSeries.coeff k ((1 + PowerSeries.C (c / N) * PowerSeries.X) ^ N))
      atTop (𝓝 (PowerSeries.coeff k (PowerSeries.rescale c (PowerSeries.exp 𝕜)))) := by
  have hcoeff : ∀ᶠ N : ℕ in atTop,
      PowerSeries.coeff k ((1 + PowerSeries.C (c / N) * PowerSeries.X) ^ N) =
        (c ^ k / (k ! : 𝕜)) * ∏ i ∈ Finset.range k, (1 - (i : 𝕜) * (N : 𝕜)⁻¹) := by
    filter_upwards [eventually_ge_atTop (max k 1)] with N hN
    have hkN : k ≤ N := (le_max_left k 1).trans hN
    have hN0 : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hk0 : (k ! : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hpow : (1 + PowerSeries.C (c / N) * PowerSeries.X) ^ N = ∑ i ∈ Finset.range (N + 1),
        PowerSeries.C ((N.choose i : 𝕜) * (c / N) ^ i) * PowerSeries.X ^ i := by
      rw [add_comm 1 _, add_pow]; refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [one_pow, mul_one, mul_pow, ← map_natCast PowerSeries.C, ← map_pow, mul_right_comm,
        ← map_mul, mul_comm ((c / ↑N) ^ i)]
    have hdesc : (k ! : 𝕜) * (N.choose k : 𝕜) = ∏ i ∈ Finset.range k, ((N : 𝕜) - i) := by
      have h := congrArg ((↑) : ℕ → 𝕜) (Nat.descFactorial_eq_factorial_mul_choose N k)
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_mul, Nat.cast_prod] at h
      exact h.symm.trans (Finset.prod_congr rfl fun i hi ↦
        Nat.cast_sub ((Finset.mem_range.mp hi).le.trans hkN))
    have hprod : ∏ i ∈ Finset.range k, (1 - (i : 𝕜) * (N : 𝕜)⁻¹) =
        (∏ i ∈ Finset.range k, ((N : 𝕜) - i)) / (N : 𝕜) ^ k := by
      rw [show (N : 𝕜) ^ k = ∏ _ ∈ Finset.range k, (N : 𝕜) by simp, ← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ by field_simp
    rw [hpow, map_sum]; simp only [PowerSeries.coeff_C_mul_X_pow, Finset.sum_ite_eq,
      Finset.mem_range, Nat.lt_succ_iff.mpr hkN, ↓reduceIte, hprod, ← hdesc, div_pow]; field_simp
  have h1 : Tendsto (fun N : ℕ ↦ ∏ i ∈ Finset.range k, (1 - (i : 𝕜) * (N : 𝕜)⁻¹)) atTop (𝓝 1) := by
    simpa using tendsto_finsetProd (Finset.range k) fun i _ ↦
      (tendsto_const_nhds (x := (1 : 𝕜))).sub (tendsto_inv_natCast_zero.const_mul (i : 𝕜))
  simpa only [mul_one, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, map_div₀, map_one,
    map_natCast, mul_one_div] using
      (h1.const_mul (c ^ k / (k ! : 𝕜))).congr' (EventuallyEq.symm hcoeff)

private theorem tendsto_coeff_of_mul_eq {𝕜 : Type*} [RCLike 𝕜] {F A B : ℕ → PowerSeries 𝕜}
    {L A₀ B₀ : PowerSeries 𝕜} (hmul : ∀ N, F N * B N = A N) (hmul₀ : L * B₀ = A₀)
    (hB_const : ∀ N, PowerSeries.constantCoeff (B N) = 1)
    (hB₀_const : PowerSeries.constantCoeff B₀ = 1)
    (hA : ∀ k, Tendsto (fun N ↦ PowerSeries.coeff k (A N)) atTop (𝓝 (PowerSeries.coeff k A₀)))
    (hB : ∀ k, Tendsto (fun N ↦ PowerSeries.coeff k (B N)) atTop (𝓝 (PowerSeries.coeff k B₀)))
    (k : ℕ) : Tendsto (fun N ↦ PowerSeries.coeff k (F N)) atTop (𝓝 (PowerSeries.coeff k L)) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hsolve (P Q : PowerSeries 𝕜) (hQ : PowerSeries.constantCoeff Q = 1) :
        PowerSeries.coeff k P = PowerSeries.coeff k (P * Q) -
          ∑ i ∈ Finset.range k, PowerSeries.coeff i P * PowerSeries.coeff (k - i) Q := by
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ PowerSeries.coeff i P * PowerSeries.coeff j Q) k, Finset.sum_range_succ,
        Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, hQ, mul_one]; ring
    simp_rw [fun N ↦ hsolve (F N) (B N) (hB_const N), hmul, hsolve L B₀ hB₀_const, hmul₀]
    exact (hA k).sub (tendsto_finsetSum (Finset.range k) fun i hi ↦
      (ih i (Finset.mem_range.mp hi)).mul (hB (k - i)))

/-- **Mixed atomic-and-dust coefficientwise limit at `Q = 1`:** augmenting `(ι, pos, p)` by `N`
dust letters of sign `b` and weight `γ / N` converges in degree `m + 1`. -/
theorem tendsto_countableAtomicTrace_add_dust_cycleWord_of_sq_eq_one {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (b : Bool) (q : 𝕜ˣ)
    (hq : (q : 𝕜) ^ 2 = 1) (p : ι → 𝕜) (hp : Summable fun a ↦ ‖p a‖) (γ : 𝕜) (m : ℕ) :
    Tendsto (fun N : ℕ ↦
        countableAtomicTrace (dustPos pos b N) q (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
          (hp.sumLex (hasSum_fintype _).summable) (m + 1) (cycleWord q (m + 1)))
      atTop (𝓝 ((∑' a, (if pos a then (1 : 𝕜) else -1) ^ m * p a ^ (m + 1)) +
        if m = 0 then γ else 0)) := by
  have hev : ∀ᶠ N : ℕ in atTop,
      atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)) =
        (if b = true then (1 : 𝕜) else -1) ^ m * γ ^ (m + 1) * ((N : 𝕜)⁻¹) ^ m := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [atomicTrace_cycleWord_of_sq_eq_one _ q hq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, div_pow, mul_left_comm, mul_div_assoc',
      pow_succ' (N : 𝕜) m, ← div_div, mul_div_cancel_left₀ _ hN0, div_eq_mul_inv, inv_pow,
      ← mul_assoc]
  refine (tendsto_const_nhds.add (Tendsto.congr' (hev.mono fun _ h ↦ h.symm) ?_)).congr fun N ↦ ?_
  · rcases m with _ | m <;> [simp; simpa using ((tendsto_inv_natCast_zero (𝕜 := 𝕜)).pow
      (m + 1)).const_mul ((if b = true then (1 : 𝕜) else -1) ^ (m + 1) * γ ^ (m + 2))]
  · rw [countableAtomicTrace_cycleWord_of_sq_eq_one (dustPos pos b N) q hq,
      atomicTrace_cycleWord_of_sq_eq_one (fun _ : Fin N ↦ b = true) q hq]
    exact (HasSum.sumLex ((TauCeti.summable_signed_pow_mul_pow pos hp m).of_norm.hasSum.congr_fun
      fun _ ↦ by simp) ((hasSum_fintype fun _ : Fin N ↦ (if b = true then (1 : 𝕜) else -1) ^ m *
        (γ / N) ^ (m + 1)).congr_fun fun _ ↦ by simp)).tsum_eq.symm

private noncomputable def dustPfac {𝕜 α : Type*} [CommRing 𝕜] [Fintype α] (pos₀ : α → Prop)
    [DecidablePred pos₀] (w₀ : α → 𝕜) (c₁ c₂ : 𝕜) : PowerSeries 𝕜 := ∏ a : α,
  if pos₀ a then 1 - PowerSeries.C (c₁ * w₀ a) * PowerSeries.X
  else 1 + PowerSeries.C (c₂ * w₀ a) * PowerSeries.X

/-- **Mixed atomic-and-dust cycle-trace coefficientwise limit:** augmenting `(ι, pos, p)` by `N`
dust letters of sign `b` and weight `γ / N` converges in degree `m + 1` to the `(m + 1)`-th
coefficient of the background series times `exp (((q : 𝕜) ^ 2 - 1) * γ * X)`. -/
theorem tendsto_countableAtomicTrace_add_dust_cycleWord {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
    [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos] (b : Bool) (q : 𝕜ˣ) (p : ι → 𝕜)
    (hp : Summable fun a ↦ ‖p a‖) (γ : 𝕜) (m : ℕ) :
    Tendsto (fun N : ℕ ↦
        countableAtomicTrace (dustPos pos b N) q (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
          (hp.sumLex (hasSum_fintype _).summable) (m + 1) (cycleWord q (m + 1)))
      atTop (𝓝 (PowerSeries.coeff m ((PowerSeries.mk fun k ↦
          countableAtomicTrace pos q p hp (k + 1) (cycleWord q (k + 1))) *
          PowerSeries.rescale (((q : 𝕜) ^ 2 - 1) * γ) (PowerSeries.exp 𝕜)) +
        ((q : 𝕜) ^ 2 - 1) ^ m * γ ^ (m + 1) / ((m + 1)! : 𝕜))) := by
  classical
  by_cases hq : (q : 𝕜) ^ 2 = 1
  · refine (tendsto_countableAtomicTrace_add_dust_cycleWord_of_sq_eq_one pos b q hq p hp γ
        m).trans_eq ?_
    simp_rw [countableAtomicTrace_cycleWord_of_sq_eq_one pos q hq p hp, hq, sub_self, zero_mul,
      PowerSeries.rescale_zero_apply, PowerSeries.constantCoeff_exp, map_one, mul_one,
      PowerSeries.coeff_mk]; rcases m with _ | m <;> simp
  · set Q : 𝕜 := (q : 𝕜) ^ 2
    set pN : ∀ N, ι ⊕ₗ Fin N → 𝕜 := fun N a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a)
    set hpN : ∀ N, Summable fun a ↦ ‖pN N a‖ := fun _ ↦ hp.sumLex (hasSum_fintype _).summable
    set F : ℕ → PowerSeries 𝕜 := fun N ↦ PowerSeries.mk fun k ↦ if k = 0 then 1 else
      (Q - 1) * countableAtomicTrace (dustPos pos b N) q (pN N) (hpN N) k (cycleWord q k)
    set F_bg : PowerSeries 𝕜 := PowerSeries.mk fun k ↦
      if k = 0 then 1 else (Q - 1) * countableAtomicTrace pos q p hp k (cycleWord q k)
    set d : 𝕜 := if b then -(Q * γ) else γ; set u : 𝕜 := if b then -γ else Q * γ
    set B : ℕ → PowerSeries 𝕜 := fun N ↦ (1 + PowerSeries.C (d / N) * PowerSeries.X) ^ N
    set A : ℕ → PowerSeries 𝕜 := fun N ↦ F_bg * (1 + PowerSeries.C (u / N) * PowerSeries.X) ^ N
    have hmul (N : ℕ) : F N * B N = A N := by
      let g₀ (s : Finset ι) : ↥s ⊕ₗ Fin N → ι ⊕ₗ Fin N := fun a ↦
        match ofLex a with | Sum.inl i => Sum.inlₗ i.val | Sum.inr k => Sum.inrₗ k
      let T (s : Finset ι) : Finset (ι ⊕ₗ Fin N) := Finset.univ.image (g₀ s)
      have hT_atTop : Tendsto T atTop atTop := tendsto_atTop_atTop.mpr fun U ↦
        ⟨U.biUnion fun a ↦ match ofLex a with | Sum.inl i => {i} | Sum.inr _ => ∅,
          fun s hs a ha ↦ Finset.mem_image.mpr (by rcases ha' : ofLex a with i | k <;>
            [exact ⟨Sum.inlₗ ⟨i, hs (Finset.mem_biUnion.mpr ⟨a, ha, by simp [ha']⟩)⟩,
              Finset.mem_univ _, ofLex.injective (by simp [g₀, ha'])⟩;
             exact ⟨Sum.inrₗ k, Finset.mem_univ _, ofLex.injective (by simp [g₀, ha'])⟩])⟩
      let e (s : Finset ι) : (↥s ⊕ₗ Fin N) ≃o ↥(T s) :=
        OrderIso.ofSurjective (OrderEmbedding.ofStrictMono
          (fun a ↦ ⟨g₀ s a, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩) fun a₁ a₂ h ↦ by
            rcases toLex.surjective a₁ with ⟨i₁ | k₁, rfl⟩ <;>
              rcases toLex.surjective a₂ with ⟨i₂ | k₂, rfl⟩ <;> simp_all [g₀, Sum.inlₗ, Sum.inrₗ])
          fun ⟨_, ha⟩ ↦ let ⟨a, _, hga⟩ := Finset.mem_image.mp ha; ⟨a, Subtype.ext hga⟩
      let FN_s (s : Finset ι) : PowerSeries 𝕜 := PowerSeries.mk fun k ↦ if k = 0 then 1 else
        (Q - 1) * atomicTrace (fun a : ↥(T s) ↦ dustPos pos b N a) q (fun a ↦ pN N a) k
          (cycleWord q k)
      let FS_s (s : Finset ι) : PowerSeries 𝕜 := PowerSeries.mk fun k ↦ if k = 0 then 1 else
        (Q - 1) * atomicTrace (fun a : ↥s ↦ pos a) q (fun a ↦ p a) k (cycleWord q k)
      have hFinEq (s : Finset ι) :
          FN_s s * B N = FS_s s * (1 + PowerSeries.C (u / N) * PowerSeries.X) ^ N := by
        let D_bg := dustPfac (fun a : ↥s ↦ pos a) (fun a ↦ p a) Q 1
        have hgenN : FN_s s * dustPfac (fun a : ↥s ⊕ₗ Fin N ↦ dustPos pos b N (e s a).val)
            (fun a ↦ pN N (e s a).val) Q 1 = dustPfac (fun a : ↥s ⊕ₗ Fin N ↦
            dustPos pos b N (e s a).val) (fun a ↦ pN N (e s a).val) 1 Q := by
          simp_rw [FN_s, ← atomicTrace_orderIso _ _ q _ _ (e s) (fun _ ↦ Iff.rfl) (fun _ ↦ rfl)]
          simpa only [Q, dustPfac, one_mul] using atomicTrace_cycleWord_generating_function
            (fun a : ↥s ⊕ₗ Fin N ↦ dustPos pos b N (e s a).val) q (fun a ↦ pN N (e s a).val)
        have hgenS : FS_s s * D_bg = dustPfac (fun a : ↥s ↦ pos a) (fun a ↦ p a) 1 Q := by
          simpa only [Q, FS_s, D_bg, dustPfac, one_mul] using
            atomicTrace_cycleWord_generating_function (fun a : ↥s ↦ pos a) q (fun a ↦ p a)
        have hprod (c₁ c₂ v : 𝕜) (hv : v = if b then -(c₁ * γ) else c₂ * γ) :
            dustPfac (fun a : ↥s ⊕ₗ Fin N ↦ dustPos pos b N (e s a).val)
                (fun a ↦ pN N (e s a).val) c₁ c₂ =
              dustPfac (fun a : ↥s ↦ pos a) (fun a ↦ p a) c₁ c₂ *
                (1 + PowerSeries.C (v / N) * PowerSeries.X) ^ N := by
          have he_app (a) : (e s a).val = g₀ s a := rfl; dsimp only [dustPfac]
          rw [← Equiv.prod_comp (toLex (α := ↥s ⊕ Fin N)), Fintype.prod_sum_type]; congr 1
          rw [show (1 + PowerSeries.C (v / N) * PowerSeries.X) ^ N =
              ∏ _ : Fin N, (1 + PowerSeries.C (v / N) * PowerSeries.X) by simp]
          exact Finset.prod_congr rfl fun k _ ↦ by cases b <;>
            simp [dustPos, he_app, hv, g₀, Sum.inrₗ, pN, sub_eq_add_neg, neg_div, mul_div_assoc]
        refine (show IsUnit D_bg from PowerSeries.isUnit_iff_constantCoeff.mpr
          (by simp [D_bg, dustPfac, map_prod, apply_ite])).mul_right_injective ?_
        calc D_bg * (FN_s s * B N) = FN_s s * (D_bg * B N) := by ring
          _ = dustPfac (fun a : ↥s ↦ pos a) (fun a ↦ p a) 1 Q *
              (1 + PowerSeries.C (u / N) * PowerSeries.X) ^ N := by
            rw [← hprod Q 1 d (by simp [d]), ← hprod 1 Q u (by simp [u])]; exact hgenN
          _ = D_bg * (FS_s s * (1 + PowerSeries.C (u / N) * PowerSeries.X) ^ N) := by
            rw [← hgenS]; ring
      ext k; have hLHS : Tendsto (fun s : Finset ι ↦ PowerSeries.coeff k (FN_s s * B N))
          atTop (𝓝 (PowerSeries.coeff k (F N * B N))) := by
        simp_rw [PowerSeries.coeff_mul]
        refine tendsto_finsetSum _ fun ⟨i, r⟩ _ ↦ Tendsto.mul_const _ ?_
        rcases i with _ | j
        · simp [F, FN_s]
        · simpa [F, FN_s] using ((tendsto_atomicTrace_finset (dustPos pos b N) q (pN N) (hpN N)
            (j + 1) (cycleWord q (j + 1))).comp hT_atTop).const_mul (Q - 1)
      refine tendsto_nhds_unique (hLHS.congr fun s ↦ congrArg (PowerSeries.coeff k) (hFinEq s)) ?_
      simp_rw [A, PowerSeries.coeff_mul]
      refine tendsto_finsetSum _ fun ⟨i, r⟩ _ ↦ Tendsto.mul_const _ ?_
      rcases i with _ | j
      · simp [F_bg, FS_s]
      · simpa [F_bg, FS_s] using
          (tendsto_atomicTrace_finset pos q p hp (j + 1) (cycleWord q (j + 1))).const_mul (Q - 1)
    let E := PowerSeries.rescale ((Q - 1) * γ) (PowerSeries.exp 𝕜)
    let L := F_bg * E; let B₀ := PowerSeries.rescale d (PowerSeries.exp 𝕜)
    let A₀ := F_bg * PowerSeries.rescale u (PowerSeries.exp 𝕜)
    have hmul₀ : L * B₀ = A₀ := by
      rw [mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add,
        show (Q - 1) * γ + d = u by cases b <;> simp [d, u] <;> ring]
    have hcoeff := tendsto_coeff_of_mul_eq hmul hmul₀ (fun N ↦ by simp [B])
      (by rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale]; simp)
      (fun k ↦ by
        simp_rw [A, A₀, PowerSeries.coeff_mul]
        exact tendsto_finsetSum _ fun ij _ ↦ (tendsto_coeff_one_add_div_pow u ij.snd).const_mul _)
      (tendsto_coeff_one_add_div_pow d) (m + 1)
    have hL_coeff : PowerSeries.coeff (m + 1) L = (Q - 1) * (PowerSeries.coeff m ((PowerSeries.mk
        fun k ↦ countableAtomicTrace pos q p hp (k + 1) (cycleWord q (k + 1))) * E) +
          (Q - 1) ^ m * γ ^ (m + 1) / ((m + 1)! : 𝕜)) := by
      rw [show L = E + PowerSeries.C (Q - 1) * PowerSeries.X * ((PowerSeries.mk fun k ↦
          countableAtomicTrace pos q p hp (k + 1) (cycleWord q (k + 1))) * E) by
        dsimp only [L]
        rw [show F_bg = 1 + PowerSeries.C (Q - 1) * PowerSeries.X * PowerSeries.mk fun k ↦
            countableAtomicTrace pos q p hp (k + 1) (cycleWord q (k + 1)) by
          ext (_ | k) <;> [simp [F_bg];
            (rw [map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul];
              simp [F_bg])]]
        ring]
      rw [map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_rescale, PowerSeries.coeff_exp, map_div₀, map_one, map_natCast,
        mul_pow, pow_succ' (Q - 1) m]; ring
    have hQ1 : Q - 1 ≠ 0 := sub_ne_zero.mpr hq
    simpa [F, hQ1, hL_coeff, mul_inv_cancel_left₀ hQ1] using hcoeff.const_mul (Q - 1)⁻¹

private theorem atomicTrace_fin_eq_empty_sumLex {𝕜 : Type*} [RCLike 𝕜] (b : Bool) (q : 𝕜ˣ)
    (γ : 𝕜) (N n : ℕ) (x : TypeAHeckeAlgebra 𝕜 q n) :
    countableAtomicTrace (dustPos (fun _ : Empty ↦ False) b N) q
        (fun a ↦ Sum.elim (fun _ ↦ (0 : 𝕜)) (fun _ ↦ γ / N) (ofLex a))
        (summable_empty.sumLex (hasSum_fintype _).summable) n x =
      atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) n x := by
  let e : Empty ⊕ₗ Fin N ≃o Fin N :=
    { toFun := fun a ↦ Sum.elim Empty.elim id (ofLex a), invFun := Sum.inrₗ
      right_inv := fun _ ↦ rfl
      left_inv := fun a ↦ by rcases toLex.surjective a with ⟨x | k, rfl⟩ <;> [exact x.elim; rfl]
      map_rel_iff' := fun {a₁ a₂} ↦ by
        rcases toLex.surjective a₁ with ⟨x | _, rfl⟩ <;>
          rcases toLex.surjective a₂ with ⟨y | _, rfl⟩ <;>
          first | exact x.elim | exact y.elim | exact Sum.Lex.inr_le_inr_iff.symm }
  rw [countableAtomicTrace_eq_atomicTrace]; refine atomicTrace_orderIso _ _ q _ _ e ?_ ?_ n x <;>
    exact fun a ↦ by rcases toLex.surjective a with ⟨x | k, rfl⟩ <;> [exact x.elim; rfl]

/-- **Pure-dust cycle-trace coefficientwise limit:** splitting weight `γ` across `N` letters of
sign `b` and weight `γ / N` converges in degree `m + 1`. -/
theorem tendsto_atomicTrace_dust_cycleWord {𝕜 : Type*} [RCLike 𝕜] (b : Bool) (q : 𝕜ˣ) (γ : 𝕜)
    (m : ℕ) :
    Tendsto (fun N : ℕ ↦
        atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)))
      atTop (𝓝 (((q : 𝕜) ^ 2 - 1) ^ m * γ ^ (m + 1) / ((m + 1)! : 𝕜))) := by
  have hlim := tendsto_countableAtomicTrace_add_dust_cycleWord (fun _ : Empty ↦ False) b q
    (fun _ ↦ (0 : 𝕜)) summable_empty γ m
  rw [show (PowerSeries.mk fun k ↦ countableAtomicTrace (fun _ : Empty ↦ False) q
      (fun _ ↦ (0 : 𝕜)) summable_empty (k + 1) (cycleWord q (k + 1))) = 0 by
    ext k; simp [countableAtomicTrace_eq_atomicTrace, atomicTrace_eq_sum], zero_mul, map_zero,
    zero_add] at hlim
  exact hlim.congr fun N ↦ atomicTrace_fin_eq_empty_sumLex b q γ N (m + 1) _

/-- **Pure-dust coefficientwise limit at `Q = 1`:** splitting weight `γ` across `N` letters of
weight `γ / N` contributes `γ` in degree `1` (`m = 0`) and `0` in higher degrees (`m ≥ 1`). -/
theorem tendsto_atomicTrace_dust_cycleWord_of_sq_eq_one {𝕜 : Type*} [RCLike 𝕜] (b : Bool)
    (q : 𝕜ˣ) (hq : (q : 𝕜) ^ 2 = 1) (γ : 𝕜) (m : ℕ) :
    Tendsto (fun N : ℕ ↦
        atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)))
      atTop (𝓝 (if m = 0 then γ else 0)) := by
  convert tendsto_atomicTrace_dust_cycleWord b q γ m using 1
  rw [hq, sub_self]; rcases m with _ | m <;> simp

private theorem tendsto_dustFactor_pow (b : Bool) (q : ℂˣ) (γ x : ℂ) :
    Tendsto (fun N : ℕ ↦ (if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
        else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)) ^ N)
      atTop (𝓝 (Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  have hlim (u v : ℂ) : Tendsto (fun N : ℕ ↦ (1 + u / N) ^ N / (1 + v / N) ^ N) atTop
      (𝓝 (Complex.exp (u - v))) := Complex.exp_sub u v ▸
    (Complex.tendsto_one_add_div_pow_exp u).div
      (Complex.tendsto_one_add_div_pow_exp v) (Complex.exp_ne_zero _)
  cases b
  · convert hlim ((q : ℂ) ^ 2 * γ * x) (γ * x) using 1 <;> [(ext N; simp [div_pow]); ring_nf]
  · convert hlim (-(γ * x)) (-((q : ℂ) ^ 2 * γ * x)) using 1 <;>
      [(ext N; simp [div_pow, sub_eq_add_neg, neg_div]); ring_nf]

/-- **Mixed atomic-and-dust cycle-trace generating limit.** Augmenting `(ι, pos, p)` by `N` dust
letters of sign `b` and weight `γ / N` converges as `N → ∞` to the background infinite cycle-trace
product times `Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x)`. -/
theorem tendsto_countableAtomicTrace_add_dust_generating_function {ι : Type*} [LinearOrder ι]
    (pos : ι → Prop) [DecidablePred pos] (b : Bool) (q : ℂˣ) (p : ι → ℂ)
    (hp : Summable fun a ↦ ‖p a‖) (γ x : ℂ)
    (hx : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ((∑' a, ‖p a‖) + ‖γ‖) * ‖x‖ < 1) :
    Tendsto (fun N : ℕ ↦ 1 + ((q : ℂ) ^ 2 - 1) * ∑' m : ℕ,
        countableAtomicTrace (dustPos pos b N) q (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
          (hp.sumLex (hasSum_fintype _).summable) (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1))
      atTop (𝓝 ((∏' a : ι, if pos a then (1 - p a * x) / (1 - (q : ℂ) ^ 2 * p a * x)
          else (1 + (q : ℂ) ^ 2 * p a * x) / (1 + p a * x)) *
        Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  have hbg := (countableAtomicTrace_cycleWord_hasProd pos q p hp
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg γ))
      (by positivity)) (norm_nonneg x)).trans_lt hx)).2
  refine Tendsto.congr' ?_ (tendsto_const_nhds.mul (tendsto_dustFactor_pow b q γ x))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hprodN := (countableAtomicTrace_cycleWord_hasProd (dustPos pos b N) q
    (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a)) (hp.sumLex (hasSum_fintype _).summable)
    (x := x) (by rwa [tsum_norm_sum_elim_const_ofLex hp (γ / N), Fintype.card_fin, norm_div,
      Complex.norm_natCast, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))])).2
  set d := if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
    else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)
  exact (hprodN.unique (HasProd.sumLex ((hbg.tprod_eq ▸ hbg).congr_fun fun i ↦ by simp)
    ((by simpa [Finset.prod_const] using hasProd_fintype (fun _ : Fin N ↦ d) :
      HasProd (fun _ : Fin N ↦ d) (d ^ N)).congr_fun fun k ↦ by
        cases b <;> simp only [dustPos_inr, Bool.false_eq_true, ↓reduceIte, Sum.inrₗ, ofLex_toLex,
          Sum.elim_inr, d] <;> ring_nf))).symm

/-- **The continuous-dust passage (`exp ((Q - 1) * γ * x)`):** splitting weight `γ` across `N`
positive (`b = true`) or negative (`b = false`) letters of weight `γ / N` converges as `N → ∞` to
`Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x)`. -/
theorem tendsto_atomicTrace_dust_generating_function (b : Bool) (q : ℂˣ) (γ x : ℂ)
    (hx : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ‖γ‖ * ‖x‖ < 1) :
    Tendsto (fun N : ℕ ↦ 1 + ((q : ℂ) ^ 2 - 1) * ∑' m : ℕ,
        atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)) *
          x ^ (m + 1))
      atTop (𝓝 (Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  simpa [atomicTrace_fin_eq_empty_sumLex] using
    tendsto_countableAtomicTrace_add_dust_generating_function (fun _ : Empty ↦ False) b q
      (fun _ ↦ (0 : ℂ)) summable_empty γ x (by simpa using hx)

end TauCeti.TypeAHeckeAlgebra
