/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.SobolevEmbedding
public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Basic.Real.ConjExponents
import TauCeti.Analysis.Sobolev.GraphStep.Coordinates
import TauCeti.Data.ENNReal.Holder

/-!
# Interior mixed Sobolev multiplication

The local gain of integrability of a scalar `W^{1,q}` function supplies mixed products with an
`L^p` factor when `p` exceeds the dimension. The two input exponents may differ, including the
critical Sobolev exponent. The output is an actual bounded bilinear operator on native spaces.

The first factor and the output may be arbitrary real normed spaces; the Sobolev factor is
scalar. Every finite `p > dim E` and `1 ≤ q ≤ p` is covered, including `q = dim E` and `q = p`.
Infinite `p` is a separate part of the mixed-product theory.

For weakly differentiable functions with finite-dimensional values, applying the scalar
embedding coordinatewise gives local bounds for the products, uniform in the bilinear map, at
order zero and, with a bounded first factor, at order one.

## Main declarations

* `W1p.exists_mixed_valueEmbedding`: automatically choose the Hölder exponent for the value.
* `W1p.mixedBilinL` and `W1p.coeFn_mixedBilinL`: the bounded bilinear product and its value.
* `W1p.exists_eLpNorm_mixed_le`: a local estimate uniform in the bilinear coefficient map.
* `W1p.memLp_mixed`: membership for actual functions, without choosing `Lp` representatives.
* `W1p.mixedBilinL_unique`: the product formula determines the operator.
* `W1p.exists_eLpNorm_le_of_holderTriple`: the local gain of integrability for weakly
  differentiable functions with finite-dimensional values.
* `W1p.exists_eLpNorm_bilin_le` and `W1p.exists_eLpNorm_bilin_add_eLpNorm_deriv_le`: local
  order-zero and order-one product bounds with a finite-dimensional Sobolev factor.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

namespace TauCeti

open MeasureTheory Metric Set TopologicalSpace Module
open scoped ENNReal NNReal Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

/-- The interior value embedding at a Hölder exponent for multiplication with `L^p`.
The strict excess of `p` over the dimension includes the critical Sobolev exponent `q = dim E`.
When `q = p`, the target exponent is infinity. -/
theorem W1p.exists_mixed_valueEmbedding {p : ℝ≥0}
    (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {V : Set E} (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ r : ℝ≥0∞, ∃ hr : 1 ≤ r,
      let : Fact (1 ≤ r) := ⟨hr⟩
      ENNReal.HolderTriple (p : ℝ≥0∞) r (q : ℝ≥0∞) ∧
        ∃ S : W1p μ Ω (q : ℝ≥0∞) →L[ℝ] Lp ℝ r (μ.restrict V),
        ∀ u, S u =ᵐ[μ.restrict V] W1p.value u := by
  rcases eq_or_lt_of_le hqp with rfl | hqp
  · exact ⟨∞, le_top, inferInstance, W1p.exists_lpInftyEmbeddingL_of_isCompact_closure
      hp hVc hVΩ⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ q)
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hpq : (q : ℝ) < p := by exact_mod_cast hqp
  have hp0 : (0 : ℝ) < p := hq0.trans hpq
  have hdiff : 0 < (p : ℝ) - q := sub_pos.2 hpq
  let s := Real.toNNReal ((p : ℝ) * q / ((p : ℝ) - q))
  have hs : (s : ℝ) = (p : ℝ) * q / ((p : ℝ) - q) :=
    Real.coe_toNNReal _ (by positivity)
  have hs0 : (0 : ℝ) < s := by
    rw [hs]
    exact div_pos (mul_pos hp0 hq0) hdiff
  have hqs_real : (q : ℝ) ≤ (s : ℝ) := by
    rw [hs]
    rw [le_div_iff₀ (sub_pos.2 hpq)]
    nlinarith
  have hqs : q ≤ s := by exact_mod_cast hqs_real
  have he : (p : ℝ)⁻¹ + (s : ℝ)⁻¹ = (q : ℝ)⁻¹ := by
    rw [hs]
    field_simp [hp0.ne', hq0.ne', hdiff.ne']
    ring
  have hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ < (finrank ℝ E : ℝ)⁻¹ := by
    have hn : (0 : ℝ) < finrank ℝ E := by exact_mod_cast finrank_pos
    have hnp : (finrank ℝ E : ℝ) < p := by exact_mod_cast hp
    have hi := (inv_lt_inv₀ hp0 hn).2 hnp
    linarith
  let : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by
    exact (Fact.out : (1 : ℝ≥0∞) ≤ q).trans (by exact_mod_cast hqs)⟩
  have hh : ENNReal.HolderTriple (p : ℝ≥0∞) (s : ℝ≥0∞) (q : ℝ≥0∞) :=
    ENNReal.HolderTriple.of_toReal (by
      simpa only [ENNReal.coe_toReal] using (show Real.HolderTriple (p : ℝ) s q from
        ⟨he, hp0, hs0⟩))
  exact ⟨s, Fact.out, hh, W1p.exists_sobolevEmbeddingL_of_subcritical_gain hqs hgap hVc hVΩ⟩

section Bilinear

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Shared norm and representative formulas for the native Hölder operator composed with
an interior Sobolev value embedding. -/
private theorem W1p.holderComp_spec {r : ℝ≥0∞} [Fact (1 ≤ r)]
    [ENNReal.HolderTriple (p : ℝ≥0∞) r (q : ℝ≥0∞)] {V : Set E}
    (S : W1p μ Ω (q : ℝ≥0∞) →L[ℝ] Lp ℝ r (μ.restrict V))
    (hS : ∀ g, S g =ᵐ[μ.restrict V] W1p.value g) (B : F →L[ℝ] ℝ →L[ℝ] H) :
    let T := (B.holderL (μ.restrict V) p r q).bilinearComp
      (ContinuousLinearMap.id ℝ _) S
    (∀ f g, T f g =ᵐ[μ.restrict V] fun x ↦ B (f x) (W1p.value g x)) ∧
      (∀ f g, ‖T f g‖ₑ ≤ ‖S‖ₑ * ‖B‖ₑ * ‖f‖ₑ * ‖g‖ₑ) := by
  dsimp only
  constructor
  · intro f g
    rw [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.holderL_apply_apply]
    filter_upwards [B.coeFn_holder (r := (q : ℝ≥0∞)) f (S g), hS g] with x hx hg
    rw [hx, hg]
  · intro f g
    rw [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply]
    calc
      _ ≤ ‖B.holderL (μ.restrict V) p r q‖ₑ * ‖f‖ₑ * ‖S g‖ₑ :=
        ContinuousLinearMap.le_opENorm₂ _ _ _
      _ ≤ ‖B‖ₑ * ‖f‖ₑ * (‖S‖ₑ * ‖g‖ₑ) := by
        gcongr
        · exact enorm_le_iff_norm_le.mpr (B.norm_holderL_le)
        · exact S.le_opENorm g
      _ = _ := by ac_rfl

/-- The zeroth-order interior mixed product as a bounded bilinear operator. The Sobolev input
is scalar; the other factor and the output are arbitrary real normed spaces. -/
private theorem W1p.exists_mixedBilinL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {V : Set E} (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (B : F →L[ℝ] ℝ →L[ℝ] H) :
    ∃ T : Lp F (p : ℝ≥0∞) (μ.restrict V) →L[ℝ]
        W1p μ Ω (q : ℝ≥0∞) →L[ℝ] Lp H (q : ℝ≥0∞) (μ.restrict V),
      ∀ f g, T f g =ᵐ[μ.restrict V] fun x ↦ B (f x) (W1p.value g x) := by
  obtain ⟨r, hr, hhr, S, hS⟩ := W1p.exists_mixed_valueEmbedding (μ := μ) hp hqp hVc hVΩ
  let : Fact (1 ≤ r) := ⟨hr⟩
  let : ENNReal.HolderTriple (p : ℝ≥0∞) r (q : ℝ≥0∞) := hhr
  exact ⟨(B.holderL (μ.restrict V) p r q).bilinearComp (ContinuousLinearMap.id ℝ _) S,
    (W1p.holderComp_spec (p := p) S hS B).1⟩

/-- Choose the bounded bilinear mixed product supplied by the interior Sobolev estimate. -/
def W1p.mixedBilinL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {V : Set E} (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (B : F →L[ℝ] ℝ →L[ℝ] H) :
    Lp F (p : ℝ≥0∞) (μ.restrict V) →L[ℝ]
      W1p μ Ω (q : ℝ≥0∞) →L[ℝ] Lp H (q : ℝ≥0∞) (μ.restrict V) :=
  (W1p.exists_mixedBilinL hp hqp hVc hVΩ B).choose

/-- The chosen mixed operator agrees almost everywhere with the actual bilinear product. -/
theorem W1p.coeFn_mixedBilinL (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {V : Set E} (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (B : F →L[ℝ] ℝ →L[ℝ] H) (f : Lp F (p : ℝ≥0∞) (μ.restrict V))
    (g : W1p μ Ω (q : ℝ≥0∞)) :
    W1p.mixedBilinL hp hqp hVc hVΩ B f g =ᵐ[μ.restrict V]
      fun x ↦ B (f x) (W1p.value g x) :=
  (W1p.exists_mixedBilinL hp hqp hVc hVΩ B).choose_spec f g

/-- One local constant controls every coefficient pairing by its bilinear operator norm. -/
theorem W1p.exists_eLpNorm_mixed_le (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {V : Set E} (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] ℝ →L[ℝ] H)
      (f : Lp F (p : ℝ≥0∞) (μ.restrict V)) (g : W1p μ Ω (q : ℝ≥0∞)),
      eLpNorm (fun x ↦ B (f x) (W1p.value g x)) q (μ.restrict V) ≤
        C * ‖B‖ₑ * ‖f‖ₑ * ‖g‖ₑ := by
  obtain ⟨r, hr, hhr, S, hS⟩ := W1p.exists_mixed_valueEmbedding (μ := μ) hp hqp hVc hVΩ
  let : Fact (1 ≤ r) := ⟨hr⟩
  let : ENNReal.HolderTriple (p : ℝ≥0∞) r (q : ℝ≥0∞) := hhr
  refine ⟨‖S‖₊, fun B f g ↦ ?_⟩
  have hT := W1p.holderComp_spec (p := p) S hS B
  rw [← eLpNorm_congr_ae (hT.1 f g), ← Lp.enorm_def]
  simpa only [enorm_eq_nnnorm] using hT.2 f g

/-- The actual mixed product lies in `L^q(V)` for every `V` with compact closure in `Ω`. -/
theorem W1p.memLp_mixed (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {V : Set E} (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (B : F →L[ℝ] ℝ →L[ℝ] H) {f : E → F} (hf : MemLp f p (μ.restrict V))
    (g : W1p μ Ω (q : ℝ≥0∞)) :
    MemLp (fun x ↦ B (f x) (W1p.value g x)) q (μ.restrict V) := by
  have hm := Lp.memLp (W1p.mixedBilinL hp hqp hVc hVΩ B (hf.toLp f) g)
  apply hm.ae_eq
  filter_upwards [W1p.coeFn_mixedBilinL hp hqp hVc hVΩ B (hf.toLp f) g,
    hf.coeFn_toLp] with x hx hf
  rw [hx, hf]

/-- The almost-everywhere product formula uniquely determines the bounded bilinear operator. -/
theorem W1p.mixedBilinL_unique (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {V : Set E} (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (B : F →L[ℝ] ℝ →L[ℝ] H)
    {T : Lp F (p : ℝ≥0∞) (μ.restrict V) →L[ℝ]
      W1p μ Ω (q : ℝ≥0∞) →L[ℝ] Lp H (q : ℝ≥0∞) (μ.restrict V)}
    (hT : ∀ f g, T f g =ᵐ[μ.restrict V] fun x ↦ B (f x) (W1p.value g x)) :
    T = W1p.mixedBilinL hp hqp hVc hVΩ B := by
  ext f g
  exact (hT f g).trans (W1p.coeFn_mixedBilinL hp hqp hVc hVΩ B f g).symm

end Bilinear

section VectorValued

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {p : ℝ≥0}

/-- **Local gain of integrability, quantitatively.** For `dim E < p` and `1 ≤ q ≤ p`, on a
compact `K ⊆ Ω` one constant bounds `‖g‖_{Lʳ(K)}` by `‖g‖_{L^q(Ω)} + ‖Dg‖_{L^q(Ω)}` for every
weakly differentiable `g` with finite-dimensional values, where `1/p + 1/r = 1/q`. -/
theorem W1p.exists_eLpNorm_le_of_holderTriple (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {r : ℝ≥0∞} [ENNReal.HolderTriple p r q] {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (g : E → G) (Dg : E → E →L[ℝ] G), HasWeakFDerivOn μ Ω g Dg →
      MemLp g q (μ.restrict Ω) → MemLp Dg q (μ.restrict Ω) →
      eLpNorm g r (μ.restrict K) ≤
        C * (eLpNorm g q (μ.restrict Ω) + eLpNorm Dg q (μ.restrict Ω)) := by
  have hKc : closure K = K := hK.isClosed.closure_eq
  obtain ⟨r', hr', hhr', S, hS⟩ := W1p.exists_mixed_valueEmbedding (μ := μ) (Ω := Ω) hp hqp
    (V := K) (by rwa [hKc]) (by rwa [hKc])
  have hrr : r = r' := ENNReal.HolderTriple.unique_of_ne_zero (p : ℝ≥0∞) r r'
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  subst hrr
  let _ : Fact (1 ≤ r) := ⟨hr'⟩
  let b := Module.finBasis ℝ G
  let P := WeakDerivStep.coordinatesL (μ := μ) (Ω := Ω) (p := q) b
  refine ⟨∑ i, ‖b i‖₊ * (‖S‖₊ * ‖P‖₊), fun g Dg hg hgq hDq ↦ ?_⟩
  set X := eLpNorm g q (μ.restrict Ω) + eLpNorm Dg q (μ.restrict Ω) with hX
  have hKm := Measure.restrict_mono_set μ hKΩ
  -- Package `g` with its weak derivative and take its scalar coordinates in `W^{1,q}(Ω)`.
  let base := ContinuousLinearMap.id ℝ (Lp G q (μ.restrict (Ω : Set E)))
  let u : WeakDerivStep μ Ω q base := WeakDerivStep.mk base (hgq.toLp g) (hDq.toLp Dg)
    ((hg.congr_ae hgq.coeFn_toLp.symm).congr_ae_deriv hDq.coeFn_toLp.symm)
  have hprev : WeakDerivStep.prev base u = hgq.toLp g := WeakDerivStep.prev_mk _ _ _ _
  have hu : ‖u‖ₑ ≤ X := by
    have h := WeakDerivStep.norm_le_norm_prev_add_norm_weakFDeriv base u
    rw [hprev, show WeakDerivStep.weakFDeriv base u = hDq.toLp Dg from
      WeakDerivStep.weakFDeriv_mk _ _ _ _] at h
    have h' : ‖u‖₊ ≤ ‖hgq.toLp g‖₊ + ‖hDq.toLp Dg‖₊ := by
      rw [← NNReal.coe_le_coe]
      push_cast
      exact h
    rw [hX, ← Lp.enorm_toLp hgq, ← Lp.enorm_toLp hDq]
    simp only [enorm_eq_nnnorm]
    exact_mod_cast h'
  have key (i : Fin (finrank ℝ G)) :
      eLpNorm (fun x ↦ b.coord i (g x)) r (μ.restrict K) ≤ ‖S‖ₑ * ‖P‖ₑ * X := by
    have hw : S (P u i) =ᵐ[μ.restrict K] fun x ↦ b.coord i (g x) := by
      filter_upwards [hS (P u i), ae_mono hKm (WeakDerivStep.value_coordinatesL_ae b u i),
        ae_mono hKm hgq.coeFn_toLp] with x hx hx' hx''
      rw [hx, hx', hprev, hx'']
    calc
      eLpNorm (fun x ↦ b.coord i (g x)) r (μ.restrict K) = ‖S (P u i)‖ₑ := by
        rw [Lp.enorm_def, eLpNorm_congr_ae hw]
      _ ≤ ‖S‖ₑ * ‖P u i‖ₑ := S.le_opENorm _
      _ ≤ ‖S‖ₑ * (‖P‖ₑ * ‖u‖ₑ) := by
        gcongr
        exact (enorm_le_iff_norm_le.2 (norm_le_pi_norm (P u) i)).trans (P.le_opENorm u)
      _ ≤ ‖S‖ₑ * ‖P‖ₑ * X := by
        rw [← mul_assoc]
        gcongr
  clear_value P
  calc
    eLpNorm g r (μ.restrict K)
        ≤ ∑ i, ‖b i‖ₑ * eLpNorm (fun x ↦ b.coord i (g x)) r (μ.restrict K) :=
      eLpNorm_le_sum_enorm_mul_eLpNorm_coord b (hgq.aestronglyMeasurable.mono_measure hKm)
    _ ≤ ∑ i, ‖b i‖ₑ * (‖S‖ₑ * ‖P‖ₑ * X) := by
      gcongr with i
      exact key i
    _ = ↑(∑ i, ‖b i‖₊ * (‖S‖₊ * ‖P‖₊)) * X := by
      push_cast
      simp only [enorm_eq_nnnorm, Finset.sum_mul, mul_assoc]

/-- **Local bound for order-zero mixed products.** For `dim E < p`, `1 ≤ q ≤ p` and a compact
`K ⊆ Ω`, one constant bounds `‖B(f, g)‖_{L^q(K)}` by
`‖B‖ ‖f‖_{Lᵖ(K)} (‖g‖_{L^q(Ω)} + ‖Dg‖_{L^q(Ω)})` for every bilinear map `B`, every `f` and
every weakly differentiable `g` on `Ω` with finite-dimensional values. -/
theorem W1p.exists_eLpNorm_bilin_le (hp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : E → F) (g : E → G) (Dg : E → E →L[ℝ] G),
      AEStronglyMeasurable f (μ.restrict K) → HasWeakFDerivOn μ Ω g Dg →
      MemLp g q (μ.restrict Ω) → MemLp Dg q (μ.restrict Ω) →
      eLpNorm (fun x ↦ B (f x) (g x)) q (μ.restrict K) ≤
        C * ‖B‖ₑ * eLpNorm f p (μ.restrict K) *
          (eLpNorm g q (μ.restrict Ω) + eLpNorm Dg q (μ.restrict Ω)) := by
  let _ := ENNReal.HolderTriple.of_le (p := (p : ℝ≥0∞)) (q := q) (by exact_mod_cast hqp)
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_le_of_holderTriple (μ := μ) (G := G)
    (r := ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹) hp hqp hK hKΩ
  refine ⟨C, fun B f g Dg hf hg hgq hDq ↦ ?_⟩
  calc
    _ ≤ ‖B‖ₑ * eLpNorm f p (μ.restrict K) *
        eLpNorm g ((q : ℝ≥0∞)⁻¹ - (p : ℝ≥0∞)⁻¹)⁻¹ (μ.restrict K) :=
      eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm B hf
        (hgq.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set μ hKΩ))
    _ ≤ ‖B‖ₑ * eLpNorm f p (μ.restrict K) *
        (C * (eLpNorm g q (μ.restrict Ω) + eLpNorm Dg q (μ.restrict Ω))) :=
      mul_le_mul_right (hC g Dg hg hgq hDq) _
    _ = _ := by ring

/-- **Local bound for order-one mixed products.** For `dim E < p`, `1 ≤ q ≤ p` and a compact
`K ⊆ Ω`, one constant bounds the `L^q(K)` norms of `B(f, g)` and of `B(Df, g) + B(f, Dg)` by
`‖B‖ (‖f‖_{L^∞(K)} + ‖Df‖_{Lᵖ(K)}) (‖g‖_{L^q(Ω)} + ‖Dg‖_{L^q(Ω)})`. At `q = p` this is the local
bound for the algebra property of `W^{1,p}`. -/
theorem W1p.exists_eLpNorm_bilin_add_eLpNorm_deriv_le (hp : (finrank ℝ E : ℝ≥0) < p)
    (hqp : q ≤ p) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : E → F) (Df : E → E →L[ℝ] F) (g : E → G)
      (Dg : E → E →L[ℝ] G),
      AEStronglyMeasurable f (μ.restrict K) → AEStronglyMeasurable Df (μ.restrict K) →
      HasWeakFDerivOn μ Ω g Dg →
      MemLp g q (μ.restrict Ω) → MemLp Dg q (μ.restrict Ω) →
      eLpNorm (fun x ↦ B (f x) (g x)) q (μ.restrict K) +
          eLpNorm (fun x ↦ B.precompL E (Df x) (g x) + B.precompR E (f x) (Dg x)) q
            (μ.restrict K) ≤
        C * ‖B‖ₑ * (eLpNorm f ∞ (μ.restrict K) + eLpNorm Df p (μ.restrict K)) *
          (eLpNorm g q (μ.restrict Ω) + eLpNorm Dg q (μ.restrict Ω)) := by
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_bilin_le (μ := μ) (F := E →L[ℝ] F) (G := G)
    (H := E →L[ℝ] H) hp hqp hK hKΩ
  refine ⟨2 + C, fun B f Df g Dg hf hDf hg hgq hDq ↦ ?_⟩
  have hKm := Measure.restrict_mono_set μ hKΩ
  set X := eLpNorm g q (μ.restrict Ω) + eLpNorm Dg q (μ.restrict Ω)
  set M := eLpNorm f ∞ (μ.restrict K)
  set N := eLpNorm Df p (μ.restrict K)
  have hgK : eLpNorm g q (μ.restrict K) ≤ X :=
    (eLpNorm_mono_measure g hKm).trans le_self_add
  have hDgK : eLpNorm Dg q (μ.restrict K) ≤ X :=
    (eLpNorm_mono_measure Dg hKm).trans le_add_self
  have h₀ : eLpNorm (fun x ↦ B (f x) (g x)) q (μ.restrict K) ≤ ‖B‖ₑ * M * X :=
    (eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm (p := ∞) B hf
      (hgq.aestronglyMeasurable.mono_measure hKm)).trans (by gcongr)
  have h₁ : eLpNorm (fun x ↦ B.precompL E (Df x) (g x)) q (μ.restrict K) ≤
      C * ‖B‖ₑ * N * X :=
    (hC (B.precompL E) Df g Dg hDf hg hgq hDq).trans (by
      gcongr
      exact enorm_le_iff_norm_le.2 (ContinuousLinearMap.norm_precompL_le E B))
  have h₂ : eLpNorm (fun x ↦ B.precompR E (f x) (Dg x)) q (μ.restrict K) ≤
      ‖B‖ₑ * M * X :=
    (eLpNorm_le_enorm_mul_eLpNorm_mul_eLpNorm (p := ∞) (B.precompR E) hf
      (hDq.aestronglyMeasurable.mono_measure hKm)).trans (by
      gcongr
      exact enorm_le_iff_norm_le.2 (ContinuousLinearMap.norm_precompR_le E B))
  have hadd := eLpNorm_add_le (μ := μ.restrict K)
    (f := fun x ↦ B.precompL E (Df x) (g x)) (g := fun x ↦ B.precompR E (f x) (Dg x))
    (Fact.out : (1 : ℝ≥0∞) ≤ q)
  calc
    _ ≤ ‖B‖ₑ * M * X + (C * ‖B‖ₑ * N * X + ‖B‖ₑ * M * X) :=
      add_le_add h₀ (hadd.trans (add_le_add h₁ h₂))
    _ = ‖B‖ₑ * (2 * M + C * N) * X := by ring
    _ ≤ ‖B‖ₑ * ((2 + C) * (M + N)) * X := by
      gcongr
      calc
        2 * M + C * N ≤ (2 + C) * M + (2 + C) * N := by gcongr <;> simp
        _ = (2 + C) * (M + N) := by ring
    _ = ↑(2 + C) * ‖B‖ₑ * (M + N) * X := by push_cast; ring

end VectorValued

end TauCeti
