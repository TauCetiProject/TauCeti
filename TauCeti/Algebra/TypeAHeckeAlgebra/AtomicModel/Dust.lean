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
import TauCeti.RingTheory.PowerSeries.PiTopology

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
  · rcases m with _ | m <;> [simp; simpa using ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := 𝕜)).pow
      (m + 1)).const_mul ((if b = true then (1 : 𝕜) else -1) ^ (m + 1) * γ ^ (m + 2))]
  · rw [countableAtomicTrace_cycleWord_of_sq_eq_one (dustPos pos b N) q hq,
      atomicTrace_cycleWord_of_sq_eq_one (fun _ : Fin N ↦ b = true) q hq]
    exact (HasSum.sumLex ((summable_signed_pow_mul_pow pos hp m).of_norm.hasSum.congr_fun fun _ ↦
      by simp) ((hasSum_fintype _).congr_fun fun _ ↦ by simp)).tsum_eq.symm

/-- Inclusion of `s ⊕ₗ Fin N` into `ι ⊕ₗ Fin N` for a finite background subset `s : Finset ι`. -/
private def dustFinsetEmbed {ι : Type*} (s : Finset ι) (N : ℕ) : ↥s ⊕ₗ Fin N → ι ⊕ₗ Fin N :=
  fun a ↦ match ofLex a with | Sum.inl i => Sum.inlₗ i.val | Sum.inr k => Sum.inrₗ k

/-- Order isomorphism between `s ⊕ₗ Fin N` and the image finset
`Finset.univ.image (dustFinsetEmbed s N)`. -/
private noncomputable def dustFinsetOrderIso {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (s : Finset ι) (N : ℕ) : (↥s ⊕ₗ Fin N) ≃o ↥(Finset.univ.image (dustFinsetEmbed s N)) :=
  OrderIso.ofSurjective (OrderEmbedding.ofStrictMono
      (fun a ↦ ⟨dustFinsetEmbed s N a, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
      fun a₁ a₂ h ↦ by rcases toLex.surjective a₁ with ⟨_ | _, rfl⟩ <;>
        rcases toLex.surjective a₂ with ⟨_ | _, rfl⟩ <;>
        simp_all [dustFinsetEmbed, Sum.inlₗ, Sum.inrₗ])
    fun ⟨_, ha⟩ ↦ let ⟨a, _, hga⟩ := Finset.mem_image.mp ha; ⟨a, Subtype.ext hga⟩

private theorem tendsto_dustFinsetImage {ι : Type*} [DecidableEq ι] (N : ℕ) :
    Tendsto (fun s : Finset ι ↦ Finset.univ.image (dustFinsetEmbed s N)) atTop atTop :=
  tendsto_atTop_atTop.mpr fun U ↦ ⟨U.biUnion fun a ↦ match ofLex a with
      | Sum.inl i => {i} | Sum.inr _ => ∅, fun s hs a ha ↦ Finset.mem_image.mpr (by
    rcases ha' : ofLex a with i | k
    · exact ⟨Sum.inlₗ ⟨i, hs (Finset.mem_biUnion.mpr ⟨a, ha, by simp [ha']⟩)⟩,
        Finset.mem_univ _, ofLex.injective (by simp [dustFinsetEmbed, ha'])⟩
    · exact ⟨Sum.inrₗ k, Finset.mem_univ _, ofLex.injective (by simp [dustFinsetEmbed, ha'])⟩)⟩

/-- Generating-series identity on a finite background `s : Finset ι` augmented with `N` dust
letters of sign `b` and constant weight `w`. -/
private theorem dustCycleSeries_finset_mul {𝕜 ι : Type*} [CommRing 𝕜] [LinearOrder ι]
    [DecidableEq ι] (pos : ι → Prop) [DecidablePred pos] (b : Bool) (q : 𝕜ˣ) (p : ι → 𝕜)
    (w : 𝕜) (N : ℕ) (s : Finset ι) :
    PowerSeries.mk (fun k ↦ if k = 0 then 1 else ((q : 𝕜) ^ 2 - 1) *
        atomicTrace (fun a : ↥(Finset.univ.image (dustFinsetEmbed s N)) ↦ dustPos pos b N a) q
          (fun a ↦ Sum.elim p (fun _ ↦ w) (ofLex a.val)) k (cycleWord q k)) *
        (1 + PowerSeries.C (if b then -((q : 𝕜) ^ 2 * w) else w) * PowerSeries.X) ^ N =
      PowerSeries.mk (fun k ↦ if k = 0 then 1 else ((q : 𝕜) ^ 2 - 1) *
          atomicTrace (fun a : ↥s ↦ pos a) q (fun a ↦ p a) k (cycleWord q k)) *
        (1 + PowerSeries.C (if b then -w else (q : 𝕜) ^ 2 * w) * PowerSeries.X) ^ N := by
  set Q : 𝕜 := (q : 𝕜) ^ 2; set pN : ι ⊕ₗ Fin N → 𝕜 := fun a ↦ Sum.elim p (fun _ ↦ w) (ofLex a)
  let e := dustFinsetOrderIso s N; let D_bg := ∏ a : ↥s,
    (cycleGeneratingFactor (fun a ↦ pos a.val) (fun a ↦ p a.val) Q 1 a : PowerSeries 𝕜)
  have hgenN := atomicTrace_cycleWord_generating_function_eq_prod
    (fun a : ↥s ⊕ₗ Fin N ↦ dustPos pos b N (e a).val) q (fun a ↦ pN (e a).val)
  simp_rw [atomicTrace_orderIso q _ (fun a ↦ dustPos pos b N a.val) _ (fun a ↦ pN a.val) e
    (fun _ ↦ Iff.rfl) (fun _ ↦ rfl)] at hgenN
  have hgenS := atomicTrace_cycleWord_generating_function_eq_prod (fun a : ↥s ↦ pos a.val) q
    (fun a ↦ p a.val)
  have hprod (c₁ c₂ v : 𝕜) (hv : v = if b then -(c₁ * w) else c₂ * w) : ∏ a : ↥s ⊕ₗ Fin N,
      (cycleGeneratingFactor (fun a ↦ dustPos pos b N (e a).val) (fun a ↦ pN (e a).val) c₁ c₂
        a : PowerSeries 𝕜) = (∏ a : ↥s, (cycleGeneratingFactor (fun a ↦ pos a.val)
      (fun a ↦ p a.val) c₁ c₂ a : PowerSeries 𝕜)) * (1 + PowerSeries.C v * PowerSeries.X) ^ N := by
    have he_app (a) : (e a).val = dustFinsetEmbed s N a := rfl
    rw [← Equiv.prod_comp (toLex (α := ↥s ⊕ Fin N)), Fintype.prod_sum_type]; congr 1
    · exact Finset.prod_congr rfl fun i _ ↦ by
        simp_rw [coe_cycleGeneratingFactor]; simp [dustPos, he_app, dustFinsetEmbed, Sum.inlₗ, pN]
    · rw [show (1 + PowerSeries.C v * PowerSeries.X) ^ N =
          ∏ _ : Fin N, (1 + PowerSeries.C v * PowerSeries.X) by simp]
      exact Finset.prod_congr rfl fun k _ ↦ by
        simp_rw [coe_cycleGeneratingFactor]
        cases b <;> simp [dustPos, he_app, hv, dustFinsetEmbed, Sum.inrₗ, pN, sub_eq_add_neg]
  refine (isUnit_prod_cycleGeneratingFactor (fun a : ↥s ↦ pos a.val) (fun a ↦ p a.val) Q 1
    ).mul_right_injective ?_
  dsimp only; rw [mul_left_comm D_bg, ← hprod Q 1 _ (by simp), hgenN,
    hprod 1 Q (if b then -w else Q * w) (by simp), ← hgenS]; ring

/-- Coefficientwise convergence of `mk (fun k ↦ if k = 0 then 1 else c * tr_seq i k) * B` from
convergence of `tr_seq i (j + 1) → tr (j + 1)`. -/
private theorem tendsto_coeff_cycleSeries_mul {𝕜 α : Type*} [Semiring 𝕜] [TopologicalSpace 𝕜]
    [ContinuousAdd 𝕜] [ContinuousMul 𝕜] {l : Filter α} (c : 𝕜) (tr_seq : α → ℕ → 𝕜)
    (tr : ℕ → 𝕜) (htr : ∀ j, Tendsto (fun i ↦ tr_seq i (j + 1)) l (𝓝 (tr (j + 1))))
    (B : PowerSeries 𝕜) (k : ℕ) :
    Tendsto (fun i ↦ PowerSeries.coeff k
        (PowerSeries.mk (fun k ↦ if k = 0 then 1 else c * tr_seq i k) * B))
      l (𝓝 (PowerSeries.coeff k (PowerSeries.mk (fun k ↦ if k = 0 then 1 else c * tr k) * B))) := by
  simp_rw [PowerSeries.coeff_mul]; refine tendsto_finsetSum _ fun ⟨j, _⟩ _ ↦ Tendsto.mul_const _ ?_
  rcases j with _ | j <;> [simpa using tendsto_const_nhds; simpa using (htr j).const_mul c]

/-- Generating-series identity for `countableAtomicTrace` of `(ι, pos, p)` augmented with `N`
dust letters of sign `b` and weight `γ / N`. -/
private theorem dustCycleSeries_mul {𝕜 ι : Type*} [RCLike 𝕜] [LinearOrder ι]
    (pos : ι → Prop) [DecidablePred pos] (b : Bool) (q : 𝕜ˣ) (p : ι → 𝕜)
    (hp : Summable fun a ↦ ‖p a‖) (γ : 𝕜) (N : ℕ) :
    PowerSeries.mk (fun k ↦ if k = 0 then 1 else ((q : 𝕜) ^ 2 - 1) *
        countableAtomicTrace (dustPos pos b N) q (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a))
          (hp.sumLex (hasSum_fintype _).summable) k (cycleWord q k)) *
        (1 + PowerSeries.C ((if b then -((q : 𝕜) ^ 2 * γ) else γ) / N) * PowerSeries.X) ^ N =
      PowerSeries.mk (fun k ↦ if k = 0 then 1 else
          ((q : 𝕜) ^ 2 - 1) * countableAtomicTrace pos q p hp k (cycleWord q k)) *
        (1 + PowerSeries.C ((if b then -γ else (q : 𝕜) ^ 2 * γ) / N) * PowerSeries.X) ^ N := by
  let := Classical.decEq ι; set pN : ι ⊕ₗ Fin N → 𝕜 := fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a)
  set hpN : Summable fun a ↦ ‖pN a‖ := hp.sumLex (hasSum_fintype _).summable; ext k
  have hLHS := tendsto_coeff_cycleSeries_mul ((q : 𝕜) ^ 2 - 1)
    (fun (s : Finset ι) k ↦ atomicTrace (fun a : ↥(Finset.univ.image (dustFinsetEmbed s N)) ↦
      dustPos pos b N a) q (fun a ↦ pN a.val) k (cycleWord q k))
    (fun k ↦ countableAtomicTrace (dustPos pos b N) q pN hpN k (cycleWord q k))
    (fun j ↦ (tendsto_atomicTrace_finset (dustPos pos b N) q pN hpN (j + 1)
      (cycleWord q (j + 1))).comp (tendsto_dustFinsetImage N))
    ((1 + PowerSeries.C ((if b then -((q : 𝕜) ^ 2 * γ) else γ) / N) * PowerSeries.X) ^ N) k
  have hRHS := tendsto_coeff_cycleSeries_mul ((q : 𝕜) ^ 2 - 1)
    (fun (s : Finset ι) k ↦ atomicTrace (fun a : ↥s ↦ pos a) q (fun a ↦ p a) k (cycleWord q k))
    (fun k ↦ countableAtomicTrace pos q p hp k (cycleWord q k))
    (fun j ↦ tendsto_atomicTrace_finset pos q p hp (j + 1) (cycleWord q (j + 1)))
    ((1 + PowerSeries.C ((if b then -γ else (q : 𝕜) ^ 2 * γ) / N) * PowerSeries.X) ^ N) k
  refine tendsto_nhds_unique (hLHS.congr fun s ↦ congrArg (PowerSeries.coeff k) ?_) hRHS
  have h := dustCycleSeries_finset_mul pos b q p (γ / N) N s
  cases b <;> simpa [neg_div, mul_div_assoc] using h

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
  · refine (tendsto_countableAtomicTrace_add_dust_cycleWord_of_sq_eq_one pos b q hq p hp γ m
      ).trans_eq ?_; simp_rw [countableAtomicTrace_cycleWord_of_sq_eq_one pos q hq p hp, hq,
        sub_self, zero_mul, PowerSeries.rescale_zero_apply, PowerSeries.constantCoeff_exp, map_one,
        mul_one, PowerSeries.coeff_mk]; rcases m with _ | m <;> simp
  · set Q : 𝕜 := (q : 𝕜) ^ 2; set d : 𝕜 := if b then -(Q * γ) else γ
    set u : 𝕜 := if b then -γ else Q * γ
    let F_bg : PowerSeries 𝕜 := PowerSeries.mk fun k ↦
      if k = 0 then 1 else (Q - 1) * countableAtomicTrace pos q p hp k (cycleWord q k)
    let E := PowerSeries.rescale ((Q - 1) * γ) (PowerSeries.exp 𝕜)
    have hmul₀ : (F_bg * E) * PowerSeries.rescale d (PowerSeries.exp 𝕜) =
        F_bg * PowerSeries.rescale u (PowerSeries.exp 𝕜) := by
      rw [mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add,
        show (Q - 1) * γ + d = u by cases b <;> simp [d, u] <;> ring]
    have hcoeff := PowerSeries.tendsto_coeff_of_mul_eq (dustCycleSeries_mul pos b q p hp γ) hmul₀
      (fun _ ↦ by simp) (by rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_rescale]; simp) (fun k ↦ by
        simp_rw [PowerSeries.coeff_mul]
        exact tendsto_finsetSum _ fun ij _ ↦
          (PowerSeries.tendsto_coeff_one_add_div_pow u ij.snd).const_mul _)
      (PowerSeries.tendsto_coeff_one_add_div_pow d) (m + 1)
    have hL_coeff := PowerSeries.coeff_succ_one_add_mul_rescale_exp (Q - 1) γ (fun k ↦
      countableAtomicTrace pos q p hp k (cycleWord q k)) m
    have hQ1 : Q - 1 ≠ 0 := sub_ne_zero.mpr hq
    simpa [Q, hQ1, F_bg, E, hL_coeff, mul_inv_cancel_left₀ hQ1] using hcoeff.const_mul (Q - 1)⁻¹

private theorem atomicTrace_fin_eq_empty_sumLex {𝕜 : Type*} [RCLike 𝕜] (b : Bool) (q : 𝕜ˣ)
    (γ : 𝕜) (N n : ℕ) (x : TypeAHeckeAlgebra 𝕜 q n) :
    countableAtomicTrace (dustPos (fun _ : Empty ↦ False) b N) q
        (fun a ↦ Sum.elim (fun _ ↦ (0 : 𝕜)) (fun _ ↦ γ / N) (ofLex a))
        (summable_empty.sumLex (hasSum_fintype _).summable) n x =
      atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) n x := by
  rw [countableAtomicTrace_eq_atomicTrace]
  refine atomicTrace_orderIso q _ _ _ _ OrderIso.emptySumLex ?_ ?_ n x <;>
    exact fun a ↦ by rcases toLex.surjective a with ⟨x | _, rfl⟩ <;> [exact x.elim; rfl]

/-- **Pure-dust cycle-trace coefficientwise limit:** splitting weight `γ` across `N` letters of
sign `b` and weight `γ / N` converges in degree `m + 1`. -/
theorem tendsto_atomicTrace_dust_cycleWord {𝕜 : Type*} [RCLike 𝕜] (b : Bool) (q : 𝕜ˣ) (γ : 𝕜)
    (m : ℕ) :
    Tendsto (fun N : ℕ ↦
        atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)))
      atTop (𝓝 (((q : 𝕜) ^ 2 - 1) ^ m * γ ^ (m + 1) / ((m + 1)! : 𝕜))) := by
  have hlim := tendsto_countableAtomicTrace_add_dust_cycleWord (fun _ : Empty ↦ False) b q
    (fun _ ↦ (0 : 𝕜)) summable_empty γ m
  rw [show (PowerSeries.mk fun k ↦ countableAtomicTrace (fun _ : Empty ↦ False) q (fun _ ↦ (0 : 𝕜))
        summable_empty (k + 1) (cycleWord q (k + 1))) = 0 from
      PowerSeries.ext fun k ↦ by simp [countableAtomicTrace_eq_atomicTrace, atomicTrace_eq_sum],
    zero_mul, map_zero, zero_add] at hlim
  exact hlim.congr fun N ↦ atomicTrace_fin_eq_empty_sumLex b q γ N (m + 1) _

/-- **Pure-dust coefficientwise limit at `Q = 1`:** splitting weight `γ` across `N` letters of
weight `γ / N` contributes `γ` in degree `1` (`m = 0`) and `0` in higher degrees (`m ≥ 1`). -/
theorem tendsto_atomicTrace_dust_cycleWord_of_sq_eq_one {𝕜 : Type*} [RCLike 𝕜] (b : Bool)
    (q : 𝕜ˣ) (hq : (q : 𝕜) ^ 2 = 1) (γ : 𝕜) (m : ℕ) :
    Tendsto (fun N : ℕ ↦ atomicTrace (fun _ : Fin N ↦ b = true) q (fun _ ↦ γ / N) (m + 1)
      (cycleWord q (m + 1))) atTop (𝓝 (if m = 0 then γ else 0)) := by
  convert tendsto_atomicTrace_dust_cycleWord b q γ m using 1; rw [hq, sub_self]; rcases m with
    _ | m <;> simp

private theorem tendsto_dustFactor_pow (b : Bool) (q : ℂˣ) (γ x : ℂ) :
    Tendsto (fun N : ℕ ↦ (if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
        else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)) ^ N)
      atTop (𝓝 (Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  have hlim (u v : ℂ) : Tendsto (fun N : ℕ ↦ (1 + u / N) ^ N / (1 + v / N) ^ N) atTop
      (𝓝 (Complex.exp (u - v))) := Complex.exp_sub u v ▸ (Complex.tendsto_one_add_div_pow_exp u).div
    (Complex.tendsto_one_add_div_pow_exp v) (Complex.exp_ne_zero _)
  cases b <;> [convert hlim ((q : ℂ) ^ 2 * γ * x) (γ * x) using 1 <;> [(ext N; simp [div_pow]);
      ring_nf]; convert hlim (-(γ * x)) (-((q : ℂ) ^ 2 * γ * x)) using 1 <;> [(ext N; simp [
      div_pow, sub_eq_add_neg, neg_div]); ring_nf]]

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
  have hbg := (countableAtomicTrace_cycleWord_hasProd pos q p hp ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg γ)) (by positivity))
    (norm_nonneg x)).trans_lt hx)).2
  refine Tendsto.congr' ?_ (tendsto_const_nhds.mul (tendsto_dustFactor_pow b q γ x))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hprodN := (countableAtomicTrace_cycleWord_hasProd (dustPos pos b N) q
    (fun a ↦ Sum.elim p (fun _ ↦ γ / N) (ofLex a)) (hp.sumLex (hasSum_fintype _).summable)
    (x := x) (by rwa [tsum_norm_sum_elim_const_ofLex hp (γ / N), Fintype.card_fin, norm_div,
      Complex.norm_natCast, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))])).2
  set d := if b then (1 - γ * x / N) / (1 - (q : ℂ) ^ 2 * γ * x / N)
    else (1 + (q : ℂ) ^ 2 * γ * x / N) / (1 + γ * x / N)
  exact (hprodN.unique (HasProd.sumLex ((hbg.tprod_eq ▸ hbg).congr_fun fun i ↦ by simp)
    ((by simpa [Finset.prod_const] using hasProd_fintype (fun _ : Fin N ↦ d) : HasProd _ (d ^ N)
      ).congr_fun fun k ↦ by cases b <;> simp only [dustPos_inr, Bool.false_eq_true, ↓reduceIte,
        Sum.inrₗ, ofLex_toLex, Sum.elim_inr, d] <;> ring_nf))).symm

/-- **The continuous-dust passage (`exp ((Q - 1) * γ * x)`):** splitting weight `γ` across `N`
positive (`b = true`) or negative (`b = false`) letters of weight `γ / N` converges as `N → ∞` to
`Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x)`. -/
theorem tendsto_atomicTrace_dust_generating_function (b : Bool) (q : ℂˣ) (γ x : ℂ)
    (hx : max 1 (max ‖(q : ℂ) ^ 2‖ ‖(q : ℂ) ^ 2 - 1‖) * ‖γ‖ * ‖x‖ < 1) :
    Tendsto (fun N : ℕ ↦ 1 + ((q : ℂ) ^ 2 - 1) * ∑' m : ℕ, atomicTrace (fun _ : Fin N ↦
        b = true) q (fun _ ↦ γ / N) (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1))
      atTop (𝓝 (Complex.exp (((q : ℂ) ^ 2 - 1) * γ * x))) := by
  simpa [atomicTrace_fin_eq_empty_sumLex] using
    tendsto_countableAtomicTrace_add_dust_generating_function (fun _ : Empty ↦ False) b q
      (fun _ ↦ (0 : ℂ)) summable_empty γ x (by simpa using hx)

end TauCeti.TypeAHeckeAlgebra
