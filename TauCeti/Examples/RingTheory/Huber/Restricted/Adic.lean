/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Huber.Padic.Basic
import TauCeti.RingTheory.Huber.Restricted.Reduction.GaussNorm
import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Examples and counterexamples for adic restricted power series

Concrete checks accompanying the adic restricted-series reduction and comparison API:

* over a discrete commutative ring `A`, `restrictedMvPowerSeriesCompletion k A` reduces to the
  polynomial ring `MvPolynomial (Fin k) A`;
* over `ℤ_[p]`, both `restrictedMvPowerSeriesCompletion k ℤ_[p]` and the unit-radius Gauss-normed
  ring `MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)` are Noetherian adic
  rings whose reductions modulo `(p · ℤ_[p]⟨X⟩) ^ m` are isomorphic to `(ZMod (p ^ m))[X₁, …, Xₖ]`;
* the geometric series `∑_{n ≥ 0} X ^ n` over `ℤ_[p]` is not restricted in either carrier;
* in zero variables, `restrictedMvPowerSeriesCompletion 0 A ≃+* A` when `A` is complete and
  separated, whereas no ring isomorphism exists when `A` is `ℤ` with the indiscrete topology
  (non-separated) or `ℤ` with the `(p)`-adic topology (non-complete);
* into `ℤ_[p]`, arbitrary values of `X` induce a unique continuous evaluation homomorphism, whereas
  into `ℚ_[p]` no continuous ring homomorphism out of `ℚ_[p]⟨X⟩` fixes `ℚ_[p]` and sends `X` to
  `p⁻¹`.
-/

open Filter Topology TauCeti TauCeti.Huber

-- Over a discrete commutative ring `A`, `A⟨X₁, …, Xₖ⟩` is the polynomial ring `A[X₁, …, Xₖ]`.
example (A : Type*) [CommRing A] [TopologicalSpace A] [DiscreteTopology A] (k : ℕ) :
    Nonempty (restrictedMvPowerSeriesCompletion k A ≃+* MvPolynomial (Fin k) A) := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact ⟨(restrictedMvPowerSeriesCompletionEquiv k A).trans
    (weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).symm⟩

section PadicIntExamples

variable (p : ℕ) [Fact p.Prime]

-- Both `restrictedMvPowerSeriesCompletion k ℤ_[p]` and `ℤ_[p]⟨X₁, …, Xₖ⟩` are Noetherian adic
-- rings.
example (k : ℕ) :
    let _ : IsAdicRing ℤ_[p] :=
      have hI : IsAdic (Ideal.span {(p : ℤ_[p])}) :=
        _root_.PadicInt.maximalIdeal_eq_span_p (p := p) ▸
          TauCeti.Huber.PadicInt.isAdic_maximalIdeal
      ⟨Ideal.span {(p : ℤ_[p])}, Submodule.fg_span_singleton _, hI,
        hI.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩
    IsAdicRing (restrictedMvPowerSeriesCompletion k ℤ_[p]) ∧
      IsNoetherianRing (restrictedMvPowerSeriesCompletion k ℤ_[p]) ∧
      IsAdicRing (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ (1 : ℝ))) ∧
      IsNoetherianRing
        (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ (1 : ℝ))) := by
  intro _
  exact ⟨inferInstance, isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k
    (_root_.PadicInt.maximalIdeal_eq_span_p (p := p) ▸ TauCeti.Huber.PadicInt.isAdic_maximalIdeal),
    inferInstance, inferInstance⟩

-- Reducing `ℤ_[p]⟨X₁, …, Xₖ⟩` modulo `(p · ℤ_[p]⟨X⟩) ^ m` yields `(ZMod (p ^ m))[X₁, …, Xₖ]`
-- in both the completed Huber carrier and the Gauss-normed carrier.
example (k m : ℕ) :
    Nonempty ((restrictedMvPowerSeriesCompletion k ℤ_[p] ⧸
        (Ideal.span {(p : ℤ_[p])}).map
          (algebraMap ℤ_[p] (restrictedMvPowerSeriesCompletion k ℤ_[p])) ^ m) ≃+*
      MvPolynomial (Fin k) (ZMod (p ^ m))) ∧
    Nonempty ((MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ (1 : ℝ)) ⧸
        (Ideal.span {(p : ℤ_[p])}).map
          (algebraMap ℤ_[p]
            (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ (1 : ℝ)))) ^ m) ≃+*
      MvPolynomial (Fin k) (ZMod (p ^ m))) := by
  have hI : IsAdic (Ideal.span {(p : ℤ_[p])}) :=
    _root_.PadicInt.maximalIdeal_eq_span_p (p := p) ▸ TauCeti.Huber.PadicInt.isAdic_maximalIdeal
  let eqZMod : (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])} ^ m) ≃+* ZMod (p ^ m) :=
    (Ideal.quotEquivOfEq (by
      rw [Ideal.span_singleton_pow, ← _root_.PadicInt.ker_toZModPow])).trans
      ((_root_.PadicInt.toZModPow m).quotientKerEquivOfSurjective (ZMod.ringHom_surjective _))
  exact ⟨⟨(quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI
      (Submodule.fg_span_singleton _) m).toRingEquiv.trans
        (MvPolynomial.mapEquiv (Fin k) eqZMod)⟩,
    ⟨(TauCeti.MvPowerSeries.quotientPowIsRestrictedSubringEquivMvPolynomialQuotient
      hI (Submodule.fg_span_singleton _) m).toRingEquiv.trans
        (MvPolynomial.mapEquiv (Fin k) eqZMod)⟩⟩

-- The geometric series `∑_{n ≥ 0} X ^ n` over `ℤ_[p]` has all coefficients equal to `1` along the
-- univariate powers, so it is restricted in neither the Huber subring nor the Gauss-normed subring.
example :
    let g : MvPowerSeries (Fin 1) ℤ_[p] := fun _ ↦ 1
    g ∉ weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set ℤ_[p])) isWeightFamily_one_weight ∧
      g ∉ MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ (1 : ℝ)) := by
  intro g
  have hg : g ∉ MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ (1 : ℝ)) := by
    intro hmem
    have hinj : Function.Injective (fun n : ℕ ↦ Finsupp.single (0 : Fin 1) n) :=
      Finsupp.single_injective 0
    have hlim : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 0) :=
      Nat.cofinite_eq_atTop ▸ (hmem.comp hinj.tendsto_cofinite).congr fun n ↦ by
        simp only [Function.comp_apply]
        change ‖(1 : ℤ_[p])‖ * _ = 1
        simp
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
  exact ⟨fun hmem ↦ hg
    (weightedRestrictedSubring_eq_isRestricted_subring (n := 1) (R := ℤ_[p]) ▸ hmem), hg⟩

-- Universal-property contrast: into the linearly topologised ring `ℤ_[p]`, every value `b` gives a
-- unique continuous `ℤ_[p]`-algebra map `ℤ_[p]⟨X⟩ →ₐ[ℤ_[p]] ℤ_[p]` (and ring map on the normed
-- carrier), whereas into `ℚ_[p]` no continuous ring map out of `ℚ_[p]⟨X⟩` fixes `ℚ_[p]` and sends
-- `X` to `p⁻¹`.
example (b : Fin 1 → ℤ_[p]) :
    (∃! ψ : restrictedMvPowerSeriesCompletion 1 ℤ_[p] →ₐ[ℤ_[p]] ℤ_[p], Continuous ψ ∧
      ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set ℤ_[p])) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion 1 ℤ_[p]) = b i) ∧
    (∃! ψ : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ (1 : ℝ)) →+* ℤ_[p],
      Continuous ψ ∧ (∀ r, ψ (algebraMap ℤ_[p] _ r) = r) ∧
        ∀ i, ψ ⟨MvPowerSeries.X i,
          MvPowerSeries.isRestricted_X (fun _ : Fin 1 ↦ (1 : ℝ)) i⟩ = b i) :=
  ⟨existsUnique_continuous_algHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology
      continuous_id b,
    TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology
      (φ := RingHom.id ℤ_[p]) continuous_id b⟩

example :
    let c : Fin 1 → ℝ := fun _ ↦ 1
    ¬ ∃ ψ : MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) c →+* ℚ_[p],
      Continuous ψ ∧ (∀ r, ψ (algebraMap ℚ_[p] _ r) = r) ∧
        ψ ⟨MvPowerSeries.X 0, MvPowerSeries.isRestricted_X c 0⟩ = (p : ℚ_[p])⁻¹ := by
  intro c
  rintro ⟨ψ, hψ, hC, hX⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  let z : MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) c :=
    algebraMap ℚ_[p] _ (p : ℚ_[p]) * ⟨MvPowerSeries.X 0, MvPowerSeries.isRestricted_X c 0⟩
  have hz_norm : ‖z‖ < 1 := by
    rw [TauCeti.MvPowerSeries.norm_lt_one_iff]
    intro ν
    have hp_inv_lt : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt)
    have hcoeff : MvPowerSeries.coeff ν (z : MvPowerSeries (Fin 1) ℚ_[p]) =
        (p : ℚ_[p]) * MvPowerSeries.coeff ν (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) ℚ_[p]) := by
      rw [Subring.coe_mul, MvPowerSeries.coe_algebraMap_isRestrictedSubring,
        MvPowerSeries.coeff_C_mul]
    rw [hcoeff, norm_mul, MvPowerSeries.coeff_X]
    split_ifs
    · simpa [Padic.norm_p] using hp_inv_lt
    · simp
  have hnilp : IsTopologicallyNilpotent (ψ z) :=
    (TauCeti.MvPowerSeries.isTopologicallyNilpotent_iff_norm_lt_one.mpr hz_norm).map hψ
  have hψz : ψ z = 1 := by
    rw [map_mul, hC, hX, mul_inv_cancel₀ hp0]
  rw [hψz, IsTopologicallyNilpotent] at hnilp
  simp only [one_pow] at hnilp
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hnilp)

end PadicIntExamples

section ZeroVariables

-- When `A` is complete and separated for its canonical additive uniformity, zero-variable
-- restricted completion recovers `A`.
example (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    ∀ [CompleteSpace A] [T0Space A], Nonempty (restrictedMvPowerSeriesCompletion 0 A ≃+* A) := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  intro _ _
  exact ⟨(restrictedMvPowerSeriesCompletionEquiv 0 A).trans
    (weightedRestrictedSubringFinZeroEquiv _)⟩

-- Non-separated counterexample: `ℤ` with the indiscrete topology has trivial completion, hence
-- `restrictedMvPowerSeriesCompletion 0 ℤ` is not isomorphic to `ℤ`.
example :
    let _ : TopologicalSpace ℤ := ⊤
    let _ : NonarchimedeanRing ℤ :=
      { toContinuousAdd := ⟨continuous_top⟩
        toContinuousMul := ⟨continuous_top⟩
        is_nonarchimedean _ hU := ⟨⊤, by simp_all [nhds_top]⟩ }
    IsEmpty (restrictedMvPowerSeriesCompletion 0 ℤ ≃+* ℤ) := by
  intro _ _
  refine ⟨fun e ↦ ?_⟩
  let _ : UniformSpace ℤ := IsTopologicalAddGroup.rightUniformSpace ℤ
  have : IsUniformAddGroup ℤ := isUniformAddGroup_of_addCommGroup
  let c := (restrictedMvPowerSeriesCompletionFinZeroEquiv (A := ℤ)).symm.toRingHom.comp
    (UniformSpace.Completion.coeRingHom : ℤ →+* UniformSpace.Completion ℤ)
  have hc : Continuous c :=
    continuous_restrictedMvPowerSeriesCompletionFinZeroEquiv_symm.comp
      (UniformSpace.Completion.continuous_coe ℤ)
  have hinsep : Inseparable (0 : ℤ) 1 := by
    rw [Inseparable, nhds_top, nhds_top]
  have h01 : c 0 = c 1 := (hinsep.map hc).eq
  rw [map_zero, map_one] at h01
  exact zero_ne_one ((map_zero e).symm.trans ((congrArg e h01).trans (map_one e)))

-- Non-complete counterexample: `ℤ` with the `(p)`-adic topology is separated and Noetherian, yet
-- `restrictedMvPowerSeriesCompletion 0 ℤ` contains `(1 + p)⁻¹` and so cannot be isomorphic to `ℤ`.
example (p : ℕ) [Fact p.Prime] :
    let _ : TopologicalSpace ℤ := (Ideal.span {(p : ℤ)}).adicTopology
    let _ : NonarchimedeanRing ℤ := (Ideal.span {(p : ℤ)}).nonarchimedean
    IsEmpty (restrictedMvPowerSeriesCompletion 0 ℤ ≃+* ℤ) := by
  intro _ _
  refine ⟨fun e ↦ ?_⟩
  let _ : UniformSpace ℤ := IsTopologicalAddGroup.rightUniformSpace ℤ
  have : IsUniformAddGroup ℤ := isUniformAddGroup_of_addCommGroup
  let C := UniformSpace.Completion ℤ
  have hI : IsAdic (Ideal.span {(p : ℤ)}) := rfl
  have hp_nilp : IsTopologicallyNilpotent ((p : ℕ) : C) := by
    have hp0 : IsTopologicallyNilpotent ((p : ℕ) : ℤ) := by
      rw [IsTopologicallyNilpotent, hI.hasBasis_nhds_zero.tendsto_right_iff]
      intro n _
      exact Filter.eventually_atTop.mpr ⟨n, fun m hm ↦ Ideal.pow_le_pow_right hm
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m)⟩
    simpa using hp0.map (φ := (UniformSpace.Completion.coeRingHom : ℤ →+* C))
      (UniformSpace.Completion.continuous_coe _)
  obtain ⟨u, hu⟩ := hp_nilp.isUnit_one_add
  let f : ℤ →+* C :=
    (restrictedMvPowerSeriesCompletionFinZeroEquiv (A := ℤ)).toRingHom.comp e.symm.toRingHom
  have hf_surj : Function.Surjective f :=
    (restrictedMvPowerSeriesCompletionFinZeroEquiv (A := ℤ)).surjective.comp e.symm.surjective
  obtain ⟨m, hm⟩ := hf_surj (↑u⁻¹ : C)
  have hcast : f m = (m : C) := eq_intCast f m
  have hmul_C : (((1 + (p : ℤ)) * m : ℤ) : C) = 1 := by
    push_cast
    rw [← hcast, hm, ← hu]
    exact Units.mul_inv u
  let ι : ℤ →+* ℤ_[p] := Int.castRingHom ℤ_[p]
  have hι_cont : Continuous ι := by
    refine continuous_of_continuousAt_zero ι ?_
    rw [ContinuousAt, map_zero,
      (TauCeti.Huber.PadicInt.isAdic_maximalIdeal (p := p)).hasBasis_nhds_zero.tendsto_right_iff]
    intro n _
    refine Filter.mem_of_superset (hI.hasBasis_nhds_zero.mem_of_mem (i := n) trivial) ?_
    intro x hx
    change ι x ∈ ((IsLocalRing.maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) : Set ℤ_[p])
    rw [SetLike.mem_coe, _root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    rw [Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨(k : ℤ_[p]), by simpa [ι] using congrArg ι hk⟩
  let extι : C →+* ℤ_[p] := UniformSpace.Completion.extensionHom ι hι_cont
  have hmul_zp : (((1 + (p : ℤ)) * m : ℤ) : ℤ_[p]) = (1 : ℤ) := by
    simpa [extι] using congrArg extι hmul_C
  have hmul_z : (1 + (p : ℤ)) * m = 1 := Int.cast_injective hmul_zp
  have hp2 : (2 : ℤ) ≤ p := mod_cast (Fact.out : p.Prime).two_le
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul_z with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

end ZeroVariables
