/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.ArchWeight
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.FiniteCharacter
public import TauCeti.NumberTheory.LFunctions.Theta.Decay
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction

/-!
# Hecke's twisted theta series of a Grossencharacter

For a presented algebraic Hecke character `χ : Grossencharacter K 𝔪`, an integral ideal `𝔞` of
`𝓞 K`, and archimedean parameters `y : realSpace K`, Hecke's twisted theta series (Neukirch VII
(8.1)) is

`θ_χ(𝔞, y) = ε(χ) + ∑_{a ∈ 𝔞} χ_f(a) * χ.harmonicFactor (σ a) * archGaussian y (σ a)`,

where `σ = mixedEmbedding K`, `ε(χ) = χ.heckeEpsilon` is `1` when `χ` has trivial finite conductor
and `χ.harmonicDegree = 0` (and `0` otherwise), and `χ_f = χ.finiteCharacter` vanishes at `0` as
well as at integers not prime to `𝔪`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.heckeTheta`: Hecke's twisted theta series `θ_χ(𝔞, y)`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.summable_heckeTheta` and
  `TauCeti.LFunctions.Grossencharacter.summable_norm_heckeTheta`: absolute convergence for positive
  parameters `y`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_mul_harmonicFactor_unit` and
  `TauCeti.LFunctions.Grossencharacter.archWeight_mul_heckeTheta_unitScale`: unit invariance of
  `χ.archWeight y * χ.heckeTheta 𝔞 y` (Neukirch VII (8.2)).
* `TauCeti.LFunctions.Grossencharacter.continuousAt_heckeTheta`: continuity at positive parameters.
* `TauCeti.LFunctions.Grossencharacter.exists_norm_heckeTheta_sub_heckeEpsilon_le` and
  `TauCeti.LFunctions.Grossencharacter.exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le`:
  exponential decay of `χ.heckeTheta 𝔞 y - χ.heckeEpsilon`.
* `TauCeti.LFunctions.Grossencharacter.heckeTheta_ofRayClassCharacter_one`: at `Modulus.one K`, the
  trivial ray class character recovers `latticeTheta`.

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. **6** (1920), 11–51.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §8, (8.1)–(8.2).
-/

public section

noncomputable section

open Complex Filter NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding TauCeti.NumberField.Units
open scoped Real Topology nonZeroDivisors

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- Every residue character value of `χ` has norm at most `1`. -/
private theorem norm_finiteCharacter_le_one (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    ‖χ.finiteCharacter a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  rw [χ.finiteCharacter_eq_residueCharacter ha]
  have : Finite (𝓞 K ⧸ 𝔪.finitePart) :=
    Ring.HasFiniteQuotients.finiteQuotient 𝔪.finitePart_ne_bot
  by_cases hu : IsUnit (Ideal.Quotient.mk 𝔪.finitePart a)
  · obtain ⟨u, hu⟩ := hu
    have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
    have hpow : ‖χ.residueCharacter (u : 𝓞 K ⧸ 𝔪.finitePart)‖ ^ orderOf u = 1 := by
      rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one,
        Units.val_one, map_one, norm_one]
    rw [← hu]
    exact le_of_eq (pow_eq_one_iff_of_nonneg (norm_nonneg _) hfin.orderOf_pos.ne' |>.mp hpow)
  · rw [MulChar.map_nonunit _ hu, norm_zero]
    exact zero_le_one

private def integerLatticeIncl (𝔞 : Ideal (𝓞 K)) :
    𝔞 → idealLattice K 1 :=
  fun a ↦ ⟨mixedEmbedding K ((a : 𝓞 K) : K),
    (mem_idealLattice K 1).mpr ⟨((a : 𝓞 K) : K), by
      have h1 : (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
          ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by simp
      change ((a : 𝓞 K) : K) ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      rw [h1]
      exact (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨a, trivial, rfl⟩, rfl⟩⟩

private theorem integerLatticeIncl_injective (𝔞 : Ideal (𝓞 K)) :
    Function.Injective (integerLatticeIncl (K := K) 𝔞) := by
  intro a b hab
  have hcoe := mixedEmbedding_injective K (congrArg Subtype.val hab)
  exact Subtype.ext (RingOfIntegers.coe_injective hcoe)

private theorem norm_archGaussian_le_exp_mul {x : mixedSpace K} {δ t : ℝ}
    (hδ : δ ≤ mixedInner K x x) (ht : 1 ≤ t) {y : realSpace K} (hy : ∀ w, t ≤ y w) :
    ‖archGaussian y x‖ ≤ Real.exp (-(Real.pi * δ / 2) * t) *
      ‖archGaussian (fun _ ↦ (1 / 2 : ℝ)) x‖ := by
  classical
  have hQ := mixedInner_self_nonneg K x
  have hsum : t * mixedInner K x x ≤ ∑ w, y w * normAtPlace w x ^ 2 := by
    rw [mixedInner_self_eq_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_right (hy w) (sq_nonneg _)
  have hsplit : δ / 2 * t + 1 / 2 * mixedInner K x x ≤ t * mixedInner K x x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hQ,
      mul_nonneg (by linarith : 0 ≤ t) (sub_nonneg.mpr hδ)]
  simp only [archGaussian_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← Finset.mul_sum, ← mixedInner_self_eq_sum]
  nlinarith [Real.pi_pos]

/-- **Hecke's twisted theta series** (Neukirch VII (8.1)) attached to a presentation `χ` of an
algebraic Hecke character, an integral ideal `𝔞` of `𝓞 K`, and archimedean parameters
`y : realSpace K`. -/
def heckeTheta (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K)) (y : realSpace K) : ℂ :=
  χ.heckeEpsilon +
    ∑' a : 𝔞, χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))

/-- The defining equation of `Grossencharacter.heckeTheta`. -/
theorem heckeTheta_def (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K)) (y : realSpace K) :
    χ.heckeTheta 𝔞 y =
      χ.heckeEpsilon +
        ∑' a : 𝔞, χ.finiteCharacter (a : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
          archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K)) :=
  (rfl)

/-- For positive archimedean parameters `y`, the norms of the terms of `χ.heckeTheta 𝔞 y` are
summable. -/
theorem summable_norm_heckeTheta (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K))
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun a : 𝔞 ↦ ‖χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))‖ := by
  let f : idealLattice K 1 → ℂ := fun x ↦
    χ.harmonicFactor (x : mixedSpace K) * archGaussian y (x : mixedSpace K)
  have hdom : Summable fun a : 𝔞 ↦ ‖f (integerLatticeIncl 𝔞 a)‖ :=
    (χ.summable_harmonicFactor_mul_archGaussian (idealLattice K 1) y hy).norm.comp_injective
      (integerLatticeIncl_injective 𝔞)
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun a ↦ ?_) hdom
  dsimp only [f, integerLatticeIncl]
  rw [norm_mul, norm_mul, mul_assoc, ← norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg (χ.harmonicFactor _ * archGaussian y _))
    (χ.norm_finiteCharacter_le_one (a : 𝓞 K))

/-- For positive archimedean parameters `y`, the defining series of `χ.heckeTheta 𝔞 y` is
summable. -/
theorem summable_heckeTheta (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K))
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    Summable fun a : 𝔞 ↦ χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K)) :=
  (χ.summable_norm_heckeTheta 𝔞 hy).of_norm

/-- On any global unit `u : (𝓞 K)ˣ`, multiplying `χ.finiteCharacter u` by
`χ.harmonicFactor (mixedEmbedding K u)` cancels all finite and archimedean signs and phases,
leaving `∏_w |u_w| ^ P_w`. -/
theorem finiteCharacter_mul_harmonicFactor_unit (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) :
    χ.finiteCharacter (u : 𝓞 K) * χ.harmonicFactor (mixedEmbedding K (u : K)) =
      ((∏ w : InfinitePlace K,
        normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w : ℝ) : ℂ) := by
  rw [χ.finiteCharacter_unit u, χ.archimedeanValue_apply,
    Units.coe_prod, χ.prod_infiniteComponent_unit_mul_harmonicFactor u]

/-- **Unit invariance of Hecke's twisted theta series** (Neukirch VII (8.2)): for any unit
`u : (𝓞 K)ˣ` and any `y : realSpace K`,
`χ.archWeight (unitScale u y) * χ.heckeTheta 𝔞 (unitScale u y) = χ.archWeight y * χ.heckeTheta 𝔞 y`.
-/
theorem archWeight_mul_heckeTheta_unitScale (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K))
    (u : (𝓞 K)ˣ) (y : realSpace K) :
    (χ.archWeight (unitScale u y) : ℂ) * χ.heckeTheta 𝔞 (unitScale u y) =
      (χ.archWeight y : ℂ) * χ.heckeTheta 𝔞 y := by
  set P : ℂ := ((∏ w : InfinitePlace K,
    normAtPlace w (mixedEmbedding K (u : K)) ^ χ.harmonicExponent w : ℝ) : ℂ)
  have hP0 : P ≠ 0 := by
    simp only [P, ofReal_ne_zero, Finset.prod_ne_zero_iff, Finset.mem_univ]
    intro w _
    refine pow_ne_zero _ ?_
    rw [normAtPlace_apply]
    exact (w.pos_iff.mpr (Units.map (algebraMap (𝓞 K) K).toMonoidHom u).ne_zero).ne'
  have hPeps : P * χ.heckeEpsilon = χ.heckeEpsilon := by
    by_cases hdeg : χ.harmonicDegree = 0
    · have hw : ∀ w, χ.harmonicExponent w = 0 := by
        classical simpa [harmonicDegree_def] using hdeg
      simp [P, hw]
    · simp [χ.heckeEpsilon_eq_zero_of_harmonicDegree_ne_zero hdeg]
  let e : 𝔞 ≃ 𝔞 :=
    { toFun a := ⟨(u : 𝓞 K) * (a : 𝓞 K), 𝔞.mul_mem_left (u : 𝓞 K) a.property⟩
      invFun a := ⟨((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (a : 𝓞 K),
        𝔞.mul_mem_left ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) a.property⟩
      left_inv a := Subtype.ext (by simp [← mul_assoc])
      right_inv a := Subtype.ext (by simp [← mul_assoc]) }
  have hterm (a : 𝔞) :
      P * (χ.finiteCharacter (a : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
          archGaussian (unitScale u y) (mixedEmbedding K ((a : 𝓞 K) : K))) =
        χ.finiteCharacter ((e a : 𝔞) : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K (((e a : 𝔞) : 𝓞 K) : K)) *
          archGaussian y (mixedEmbedding K (((e a : 𝔞) : 𝓞 K) : K)) := by
    have hP : P = χ.finiteCharacter (u : 𝓞 K) * χ.harmonicFactor (mixedEmbedding K (u : K)) :=
      (χ.finiteCharacter_mul_harmonicFactor_unit u).symm
    have hcoe : (((e a : 𝔞) : 𝓞 K) : K) = (u : K) * ((a : 𝓞 K) : K) := by
      simp [e]
    have he_coe : ((e a : 𝔞) : 𝓞 K) = (u : 𝓞 K) * (a : 𝓞 K) := rfl
    rw [hP, hcoe, he_coe, map_mul (χ.finiteCharacter : 𝓞 K →*₀ ℂ),
      map_mul (mixedEmbedding K), ← unitSMul_smul, archGaussian_unit_smul,
      χ.harmonicFactor_unit_smul]
    ring
  set S₁ : ℂ := ∑' a : 𝔞, χ.finiteCharacter (a : 𝓞 K) *
    χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
    archGaussian (unitScale u y) (mixedEmbedding K ((a : 𝓞 K) : K))
  set S₂ : ℂ := ∑' a : 𝔞, χ.finiteCharacter (a : 𝓞 K) *
    χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
    archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))
  have htsum : P * S₁ = S₂ := by
    have hmul : P * S₁ = ∑' a : 𝔞, P * (χ.finiteCharacter (a : 𝓞 K) *
        χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
        archGaussian (unitScale u y) (mixedEmbedding K ((a : 𝓞 K) : K))) := by
      by_cases hs : Summable fun a : 𝔞 ↦ χ.finiteCharacter (a : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
          archGaussian (unitScale u y) (mixedEmbedding K ((a : 𝓞 K) : K))
      · exact (hs.hasSum.mul_left P).tsum_eq.symm
      · have hs' : ¬ Summable fun a : 𝔞 ↦ P * (χ.finiteCharacter (a : 𝓞 K) *
            χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
            archGaussian (unitScale u y) (mixedEmbedding K ((a : 𝓞 K) : K))) :=
          fun h ↦ hs ((summable_mul_left_iff hP0).mp h)
        dsimp only [S₁]
        rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable hs', mul_zero]
    rw [hmul, tsum_congr hterm]
    exact e.tsum_eq fun b ↦ χ.finiteCharacter (b : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((b : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((b : 𝓞 K) : K))
  rw [χ.archWeight_unitScale u y, ofReal_mul, heckeTheta_def, heckeTheta_def]
  calc (P * (χ.archWeight y : ℂ)) * (χ.heckeEpsilon + S₁)
      = (χ.archWeight y : ℂ) * (P * χ.heckeEpsilon + P * S₁) := by ring
    _ = (χ.archWeight y : ℂ) * (χ.heckeEpsilon + S₂) := by rw [hPeps, htsum]

/-- Hecke's twisted theta series is continuous at every positive parameter `y₀ : realSpace K`. -/
theorem continuousAt_heckeTheta (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K))
    {y₀ : realSpace K} (hy₀ : ∀ w, 0 < y₀ w) : ContinuousAt (χ.heckeTheta 𝔞) y₀ := by
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_min_image Finset.univ y₀ Finset.univ_nonempty
  set δ := y₀ w₀ / 2
  have hδ : 0 < δ := half_pos (hy₀ w₀)
  have hU : IsOpen {y : realSpace K | ∀ w, δ < y w} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w ↦ isOpen_lt continuous_const (continuous_apply w)
  have hy₀U : y₀ ∈ {y : realSpace K | ∀ w, δ < y w} := fun w ↦
    (half_lt_self (hy₀ w₀)).trans_le (hw₀ w (Finset.mem_univ w))
  let f : idealLattice K 1 → ℂ := fun x ↦
    χ.harmonicFactor (x : mixedSpace K) * archGaussian (fun _ ↦ δ) (x : mixedSpace K)
  have hdom : Summable fun a : 𝔞 ↦ ‖f (integerLatticeIncl 𝔞 a)‖ :=
    (χ.summable_harmonicFactor_mul_archGaussian (idealLattice K 1)
      (fun _ ↦ δ) (fun _ ↦ hδ)).norm.comp_injective (integerLatticeIncl_injective 𝔞)
  have hcont : ContinuousOn (fun y ↦ ∑' a : 𝔞, χ.finiteCharacter (a : 𝓞 K) *
      χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
      archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))) {y : realSpace K | ∀ w, δ < y w} := by
    refine continuousOn_tsum (fun a ↦
      (continuous_const.mul (continuous_archGaussian _)).continuousOn) hdom fun a y hy ↦ ?_
    calc ‖χ.finiteCharacter (a : 𝓞 K) *
          χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K)) *
          archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))‖
        = (‖χ.finiteCharacter (a : 𝓞 K)‖ *
            ‖χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K))‖) *
            ‖archGaussian y (mixedEmbedding K ((a : 𝓞 K) : K))‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (1 * ‖χ.harmonicFactor (mixedEmbedding K ((a : 𝓞 K) : K))‖) *
            ‖archGaussian (fun _ ↦ δ) (mixedEmbedding K ((a : 𝓞 K) : K))‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_right (χ.norm_finiteCharacter_le_one _)
            (norm_nonneg _)) (norm_archGaussian_le (fun w ↦ (hy w).le) _)
            (norm_nonneg _) (by positivity)
      _ = ‖f (integerLatticeIncl 𝔞 a)‖ := by
          simp only [one_mul, f, integerLatticeIncl, norm_mul]
  rw [funext (χ.heckeTheta_def 𝔞)]
  exact continuousAt_const.add (hcont.continuousAt (hU.mem_nhds hy₀U))

/-- Exponential decay of `χ.heckeTheta 𝔞 y - χ.heckeEpsilon` when every parameter coordinate is
at least `t ≥ 1`. -/
theorem exists_norm_heckeTheta_sub_heckeEpsilon_le (χ : Grossencharacter K 𝔪) (𝔞 : Ideal (𝓞 K)) :
    ∃ c > 0, ∃ C ≥ 0, ∀ t : ℝ, 1 ≤ t → ∀ y : realSpace K, (∀ w, t ≤ y w) →
      ‖χ.heckeTheta 𝔞 y - χ.heckeEpsilon‖ ≤ C * Real.exp (-c * t) := by
  classical
  obtain ⟨δ, hδ, hL⟩ := exists_pos_le_mixedInner (idealLattice K 1)
  let f : idealLattice K 1 → ℂ := fun x ↦
    χ.harmonicFactor (x : mixedSpace K) *
      archGaussian (fun _ ↦ (1 / 2 : ℝ)) (x : mixedSpace K)
  let b : {a : 𝔞 // a ≠ 0} → ℝ := fun a ↦ ‖f (integerLatticeIncl 𝔞 (a : 𝔞))‖
  have hb : Summable b :=
    ((χ.summable_harmonicFactor_mul_archGaussian (idealLattice K 1)
      (fun _ ↦ (1 / 2 : ℝ)) (fun _ ↦ by norm_num)).norm.comp_injective
      (integerLatticeIncl_injective 𝔞)).subtype _
  refine ⟨Real.pi * δ / 2, by positivity, ∑' a, b a,
    tsum_nonneg (fun _ ↦ norm_nonneg _), fun t ht y hy ↦ ?_⟩
  have hy_pos : ∀ w, 0 < y w := fun w ↦ lt_of_lt_of_le zero_lt_one (ht.trans (hy w))
  have hsum := χ.summable_heckeTheta 𝔞 hy_pos
  rw [heckeTheta_def, add_sub_cancel_left, ← hsum.sum_add_tsum_subtype_compl {0}]
  simp only [Finset.sum_singleton, ZeroMemClass.coe_zero, map_zero, zero_mul, zero_add]
  let e : {a : 𝔞 // a ≠ 0} ≃ {a : 𝔞 // a ∉ ({0} : Finset 𝔞)} :=
    Equiv.subtypeEquivRight fun a ↦ by simp
  rw [← e.tsum_eq]
  have hle : ∀ a : {a : 𝔞 // a ≠ 0},
      ‖χ.finiteCharacter ((a : 𝔞) : 𝓞 K) *
        χ.harmonicFactor (mixedEmbedding K (((a : 𝔞) : 𝓞 K) : K)) *
        archGaussian y (mixedEmbedding K (((a : 𝔞) : 𝓞 K) : K))‖ ≤
        Real.exp (-(Real.pi * δ / 2) * t) * b a := fun a ↦ by
    have ha0 : integerLatticeIncl 𝔞 (a : 𝔞) ≠ 0 := fun h ↦
      a.property (integerLatticeIncl_injective 𝔞 (h.trans (Subtype.ext (by
        simp [integerLatticeIncl]))))
    have hdec := norm_archGaussian_le_exp_mul (hL _ ha0) ht hy
    rw [norm_mul, norm_mul]
    calc ‖χ.finiteCharacter ((a : 𝔞) : 𝓞 K)‖ *
          ‖χ.harmonicFactor (mixedEmbedding K (((a : 𝔞) : 𝓞 K) : K))‖ *
          ‖archGaussian y (mixedEmbedding K (((a : 𝔞) : 𝓞 K) : K))‖
        ≤ 1 * ‖χ.harmonicFactor (mixedEmbedding K (((a : 𝔞) : 𝓞 K) : K))‖ *
            (Real.exp (-(Real.pi * δ / 2) * t) *
              ‖archGaussian (fun _ ↦ (1 / 2 : ℝ))
                (mixedEmbedding K (((a : 𝔞) : 𝓞 K) : K))‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (χ.norm_finiteCharacter_le_one _)
            (norm_nonneg _)) hdec (norm_nonneg _) (by positivity)
      _ = Real.exp (-(Real.pi * δ / 2) * t) * b a := by
          simp only [b, f, integerLatticeIncl, norm_mul]; ring
  calc ‖∑' a : {a : 𝔞 // a ≠ 0}, _‖
      ≤ ∑' a, Real.exp (-(Real.pi * δ / 2) * t) * b a :=
        tsum_of_norm_bounded (hb.mul_left _).hasSum hle
    _ = (∑' a, b a) * Real.exp (-(Real.pi * δ / 2) * t) := by
        rw [tsum_mul_left, mul_comm]

/-- Uniform stretched-exponential decay of `χ.heckeTheta 𝔞 (surfaceScale x u) - χ.heckeEpsilon`
along any bounded subset of `normOneSurface K`. -/
theorem exists_norm_heckeTheta_surfaceScale_sub_heckeEpsilon_le (χ : Grossencharacter K 𝔪)
    (𝔞 : Ideal (𝓞 K)) {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    (hS : D ⊆ normOneSurface K) :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop, ∀ x ∈ D,
      ‖χ.heckeTheta 𝔞 (surfaceScale x u) - χ.heckeEpsilon‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨b, hb, hbx⟩ := exists_pos_le_of_isBounded_normOneSurface hD hS
  obtain ⟨c, hc, C, hC, htheta⟩ := χ.exists_norm_heckeTheta_sub_heckeEpsilon_le 𝔞
  have hn : 0 < (Module.finrank ℚ K : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)))
  have hu : Tendsto (fun u : ℝ ↦ b * u ^ (Module.finrank ℚ K : ℝ)⁻¹) atTop atTop :=
    (tendsto_rpow_atTop hn).const_mul_atTop hb
  refine ⟨c * b, mul_pos hc hb, C, hC, ?_⟩
  filter_upwards [hu.eventually_ge_atTop 1, eventually_ge_atTop (0 : ℝ)] with u hu hu0 x hx
  have h := htheta (b * u ^ (Module.finrank ℚ K : ℝ)⁻¹) hu (surfaceScale x u) fun w ↦ by
    rw [surfaceScale_apply]
    simpa only [one_div] using
      mul_le_mul_of_nonneg_right (hbx x hx w)
        (Real.rpow_nonneg hu0 (Module.finrank ℚ K : ℝ)⁻¹)
  simpa only [neg_mul, mul_assoc] using h

/-- For the trivial ray class character at `Modulus.one K`, `heckeTheta` recovers `latticeTheta`
of the corresponding ideal lattice at all positive parameters `y`. -/
theorem heckeTheta_ofRayClassCharacter_one (𝔞 : (Ideal (𝓞 K))⁰)
    {y : realSpace K} (hy : ∀ w, 0 < y w) :
    (ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))).heckeTheta
        (𝔞 : Ideal (𝓞 K)) y =
      latticeTheta (idealLattice K (FractionalIdeal.mk0 K 𝔞)) y := by
  classical
  set χ := ofRayClassCharacter (1 : RayClassCharacter (Modulus.one K))
  have hfin {a : 𝓞 K} (ha : a ≠ 0) : χ.finiteCharacter a = 1 := by
    rw [χ.finiteCharacter_eq_residueCharacter ha]
    have hsub : Subsingleton (𝓞 K ⧸ (Modulus.one K).finitePart) := by
      rw [Modulus.one_finitePart]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Subsingleton.elim (Ideal.Quotient.mk (Modulus.one K).finitePart a) 1, map_one]
  have he : ∀ x : mixedSpace K, x ∈ idealLattice K (FractionalIdeal.mk0 K 𝔞) ↔
      ∃ a : (𝔞 : Ideal (𝓞 K)), mixedEmbedding K ((a : 𝓞 K) : K) = x := by
    intro x
    rw [mem_idealLattice]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ ((𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := hz
      rw [FractionalIdeal.mem_coeIdeal (𝓞 K)⁰] at hz'
      obtain ⟨a, ha, rfl⟩ := hz'
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨((a : 𝓞 K) : K), ?_, rfl⟩
      exact (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨a, a.property, rfl⟩
  let e : {a : (𝔞 : Ideal (𝓞 K)) // a ≠ 0} ≃
      {x : idealLattice K (FractionalIdeal.mk0 K 𝔞) // x ≠ 0} :=
    { toFun a := ⟨⟨mixedEmbedding K (((a : (𝔞 : Ideal (𝓞 K))) : 𝓞 K) : K),
        (he _).mpr ⟨a, rfl⟩⟩, fun h ↦ a.property (Subtype.ext (RingOfIntegers.coe_injective
        (mixedEmbedding_injective K (by simpa using congrArg Subtype.val h))))⟩
      invFun x :=
        ⟨((he (x : mixedSpace K)).mp x.val.property).choose, fun ha ↦
          x.property (Subtype.ext (by
            have hspec := ((he (x : mixedSpace K)).mp x.val.property).choose_spec
            rw [← hspec, ha]
            simp))⟩
      left_inv a := by
        ext1
        have hspec := ((he _).mp ((he _).mpr ⟨a.val, rfl⟩)).choose_spec
        exact Subtype.ext (RingOfIntegers.coe_injective (mixedEmbedding_injective K hspec))
      right_inv x := by
        ext1; ext1
        exact ((he (x : mixedSpace K)).mp x.val.property).choose_spec }
  rw [heckeTheta_def, heckeEpsilon_ofRayClassCharacter_one,
    ← (χ.summable_heckeTheta (𝔞 : Ideal (𝓞 K)) hy).sum_add_tsum_subtype_compl {0}]
  simp only [Finset.sum_singleton, ZeroMemClass.coe_zero, map_zero, zero_mul, zero_add]
  let e0 : {a : (𝔞 : Ideal (𝓞 K)) // a ≠ 0} ≃
      {a : (𝔞 : Ideal (𝓞 K)) // a ∉ ({0} : Finset (𝔞 : Ideal (𝓞 K)))} :=
    Equiv.subtypeEquivRight fun a ↦ by simp
  rw [← e0.tsum_eq, latticeTheta_eq_one_add _ y hy, ← e.tsum_eq]
  congr 1
  refine tsum_congr fun a ↦ ?_
  have ha0 : ((a : (𝔞 : Ideal (𝓞 K))) : 𝓞 K) ≠ 0 := fun h ↦
    a.property (Subtype.ext h)
  dsimp only [e0, χ]
  rw [Equiv.subtypeEquivRight_apply, hfin ha0, harmonicFactor_ofRayClassCharacter_one,
    one_mul, one_mul]
  rfl

end TauCeti.LFunctions.Grossencharacter
