/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.AdicCompletion.Noetherian
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Huber.Completion.Noetherian
import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.Restricted.Comparison
import TauCeti.RingTheory.Huber.Restricted.Limit

/-!
# Examples and boundary checks for restricted power series over adic and normed bases

This file checks the main comparisons and boundary hypotheses for restricted power series:

* Over a discrete commutative ring `A`, both the uncompleted restricted subring and the completed
  algebra `restrictedMvPowerSeriesCompletion k A` collapse to `MvPolynomial (Fin k) A`.
* Over the `(p)`-adic noetherian ring `ℤ_[p]`, the Gauss-norm unit-radius restricted power series
  subring `ℤ_[p]⟨X₁, …, Xₖ⟩` is noetherian, `(p)`-adically complete, and its quotient modulo
  `(p · ℤ_[p]⟨X₁, …, Xₖ⟩) ^ m` (`m ≠ 0`) is isomorphic to `MvPolynomial (Fin k) (ZMod (p ^ m))`.
* The geometric series `∑_{n ≥ 0} X₀ⁿ` in `MvPowerSeries (Fin 1) ℤ_[p]` inverts `1 - X₀` formally
  but is not restricted, since its constant coefficients `1` do not tend to `0` along `cofinite`.
* At `k = 0`, `restrictedMvPowerSeriesCompletion 0 A ≃+* A` holds for complete Hausdorff
  nonarchimedean rings, and fails as soon as either Hausdorffness (`ℤ[X]` with the indiscrete
  `(⊤)`-adic topology) or completeness (`ℤ[X]` with the `(2)`-adic topology) is omitted.
* Over `ℤ_[p]` (`IsLinearTopology`), every tuple `b : Fin k → ℤ_[p]` gives a unique continuous
  evaluation `ℤ_[p]`-algebra homomorphism, whereas `ℚ_[p]` is not linearly topologized and
  evaluating `X₀` at `p⁻¹` (`‖p⁻¹‖ = p > 1`) admits no continuous extension to `ℚ_[p]⟨X₀⟩`.
-/

namespace TauCeti.Examples

open Filter Polynomial Topology UniformSpace TauCeti.Huber

/-! ### Discrete coefficient rings -/

section Discrete

variable (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [DiscreteTopology A]

-- Over a discrete ring, the uncompleted restricted series ring is `MvPolynomial (Fin k) A`.
noncomputable example :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ≃+*
      MvPolynomial (Fin k) A :=
  (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight).symm

-- Over a discrete ring, the completed algebra `A⟨X₁, …, Xₖ⟩` is also `MvPolynomial (Fin k) A`.
noncomputable example :
    restrictedMvPowerSeriesCompletion k A ≃+* MvPolynomial (Fin k) A :=
  (restrictedMvPowerSeriesCompletionEquiv k A).trans
    (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight).symm

end Discrete

/-! ### `ℤ_[p]⟨X⟩`: noetherianity, `(p)`-adic completeness, and `ZMod (p ^ m)[X]` quotients -/

section PadicIntegers

variable (p : ℕ) [Fact p.Prime] (k : ℕ)

-- `ℤ_[p]⟨X₁, …, Xₖ⟩` is noetherian and `(p)`-adically complete.
example :
    IsNoetherianRing (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)) ∧
      IsAdicComplete
        ((Ideal.span {(p : ℤ_[p])}).map
          (algebraMap ℤ_[p]
            (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1))))
        (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)) := by
  have hadic : IsAdic (Ideal.span {(p : ℤ_[p])}) :=
    _root_.PadicInt.maximalIdeal_eq_span_p (p := p) ▸ PadicInt.isAdic_maximalIdeal
  exact ⟨isNoetherianRing_isRestricted_subring_of_isAdic (k := k) hadic,
    isAdicComplete_map_algebraMap_isRestricted_subring (k := k) hadic
      (Submodule.fg_span_singleton _)⟩

-- Modulo `(p · ℤ_[p]⟨X₁, …, Xₖ⟩) ^ m` (`m ≠ 0`), `ℤ_[p]⟨X₁, …, Xₖ⟩` is `(ℤ / p^m ℤ)[X₁, …, Xₖ]`.
noncomputable example {m : ℕ} (hm : m ≠ 0) :
    (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1) ⧸
        (((Ideal.span {(p : ℤ_[p])}).map
          (algebraMap ℤ_[p]
            (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)))) ^ m)) ≃+*
      MvPolynomial (Fin k) (ZMod (p ^ m)) := by
  have hadic : IsAdic (Ideal.span {(p : ℤ_[p])}) :=
    _root_.PadicInt.maximalIdeal_eq_span_p (p := p) ▸ PadicInt.isAdic_maximalIdeal
  exact (quotientIsRestrictedSubringPowEquivMvPolynomialQuotient (k := k) hadic
    (Submodule.fg_span_singleton _) hm).toRingEquiv.trans
    (MvPolynomial.mapEquiv (Fin k)
      ((Ideal.quotEquivOfEq (Ideal.span_singleton_pow (p : ℤ_[p]) m)).trans
        (_root_.PadicInt.quotientSpanPowEquivZMod m)))

-- The formal geometric series `∑_{n ≥ 0} X₀ⁿ` inverts `1 - X₀` in `MvPowerSeries (Fin 1) ℤ_[p]`,
-- yet belongs to neither the Gauss-norm restricted subring nor the topological restricted subring.
example :
    let g : MvPowerSeries (Fin 1) ℤ_[p] := fun _ ↦ 1
    (1 - MvPowerSeries.X (0 : Fin 1)) * g = 1 ∧
      ¬ MvPowerSeries.IsRestricted (fun _ : Fin 1 ↦ 1) g ∧
      ¬ TauCeti.Huber.IsRestricted g := by
  intro g
  have hgcoeff (μ : Fin 1 →₀ ℕ) : MvPowerSeries.coeff μ g = 1 := rfl
  have hmul : (1 - MvPowerSeries.X (0 : Fin 1)) * g = 1 := by
    apply MvPowerSeries.ext
    intro ν
    rw [sub_mul, one_mul, map_sub, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul,
      MvPowerSeries.coeff_one]
    by_cases hν : ν = 0
    · subst hν
      have hnot : ¬ Finsupp.single (0 : Fin 1) 1 ≤ 0 := fun h ↦ by simpa using h 0
      simp only [hnot, ite_false, ite_true, hgcoeff, sub_zero]
    · have hle : Finsupp.single (0 : Fin 1) 1 ≤ ν := by
        intro i
        rcases Finsupp.support_nonempty_iff.mpr hν with ⟨j, hj⟩
        have hj0 : ν 0 ≠ 0 := by simpa [Subsingleton.elim j 0] using Finsupp.mem_support_iff.mp hj
        simpa [Subsingleton.elim i 0] using Nat.one_le_iff_ne_zero.mpr hj0
      simp [hν, hle, hgcoeff]
  have hnotHuber : ¬ TauCeti.Huber.IsRestricted g := by
    rw [TauCeti.Huber.isRestricted_iff_coeff]
    simp only [hgcoeff]
    intro hg
    have : Infinite (Fin 1 →₀ ℕ) :=
      Infinite.of_injective (Finsupp.single (0 : Fin 1)) (Finsupp.single_injective 0)
    have : (cofinite : Filter (Fin 1 →₀ ℕ)).NeBot := Filter.cofinite_neBot
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hg)
  exact ⟨hmul, mt isRestricted_iff_isRestricted_one.mpr hnotHuber, hnotHuber⟩

end PadicIntegers

/-! ### Zero variables: `A⟨⟩ ≃+* A` and sharpness of completeness and separatedness -/

section ZeroVariables

-- When `A` is complete and Hausdorff, `restrictedMvPowerSeriesCompletion 0 A` is isomorphic to `A`.
noncomputable example (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [NonarchimedeanRing A] [CompleteSpace A] [T0Space A] :
    restrictedMvPowerSeriesCompletion 0 A ≃+* A :=
  (restrictedMvPowerSeriesCompletionEquiv 0 A).trans
    (weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A)))

-- Dropping separatedness (`T0Space`): `ℤ[X]` with the indiscrete `(⊤)`-adic topology is complete
-- and nonarchimedean, not `T0`, and `ℤ[X]⟨⟩` is the zero ring so `ℤ[X]⟨⟩ ≃+* ℤ[X]` is empty.
example :
    letI : WithIdeal ℤ[X] := ⟨⊤⟩
    CompleteSpace ℤ[X] ∧ ¬ T0Space ℤ[X] ∧
      IsEmpty (restrictedMvPowerSeriesCompletion 0 ℤ[X] ≃+* ℤ[X]) := by
  let _ : WithIdeal ℤ[X] := ⟨⊤⟩
  have hI : IsAdic (⊤ : Ideal ℤ[X]) := rfl
  have hcomp : CompleteSpace ℤ[X] :=
    hI.isPrecomplete_iff.mp ⟨fun _ _ ↦ ⟨0, fun _ ↦
      SModEq.zero.mpr (by rw [smul_eq_mul, Ideal.mul_top, Ideal.top_pow]; exact Submodule.mem_top)⟩⟩
  have hnotT0 : ¬ T0Space ℤ[X] := by
    intro _
    exact not_subsingleton ℤ[X] (hI.isHausdorff_iff.mpr inferInstance).subsingleton
  have hempty : IsEmpty (restrictedMvPowerSeriesCompletion 0 ℤ[X] ≃+* ℤ[X]) := by
    refine ⟨fun e ↦ ?_⟩
    have hadicC :
        IsAdicComplete ((⊤ : Ideal ℤ[X]).map (Completion.coeRingHom : ℤ[X] →+* Completion ℤ[X]))
          (Completion ℤ[X]) :=
      hI.isAdicComplete_map_coeRingHom ⟨{1}, by simp⟩
    have htop : (⊤ : Ideal ℤ[X]).map (Completion.coeRingHom : ℤ[X] →+* Completion ℤ[X]) = ⊤ := by
      refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
      have h1 := Ideal.mem_map_of_mem (Completion.coeRingHom : ℤ[X] →+* Completion ℤ[X])
        (Submodule.mem_top : (1 : ℤ[X]) ∈ ⊤)
      rwa [map_one] at h1
    have : Subsingleton (Completion ℤ[X]) := (htop ▸ hadicC.toIsHausdorff).subsingleton
    have : Subsingleton (restrictedMvPowerSeriesCompletion 0 ℤ[X]) :=
      (restrictedMvPowerSeriesCompletionFinZeroEquiv (A := ℤ[X])).toEquiv.subsingleton
    exact not_subsingleton ℤ[X] e.symm.toEquiv.subsingleton
  exact ⟨hcomp, hnotT0, hempty⟩

-- Dropping completeness (`CompleteSpace`): `ℤ[X]` with the `(2)`-adic topology is Hausdorff and
-- nonarchimedean, not complete, and `3` becomes a unit in `ℤ[X]⟨⟩` so `ℤ[X]⟨⟩ ≃+* ℤ[X]` is empty.
example :
    letI : WithIdeal ℤ[X] := ⟨Ideal.span {(2 : ℤ[X])}⟩
    T0Space ℤ[X] ∧ ¬ CompleteSpace ℤ[X] ∧
      IsEmpty (restrictedMvPowerSeriesCompletion 0 ℤ[X] ≃+* ℤ[X]) := by
  let _ : WithIdeal ℤ[X] := ⟨Ideal.span {(2 : ℤ[X])}⟩
  have hI : IsAdic (Ideal.span {(2 : ℤ[X])}) := rfl
  have hnot2 : ¬ IsUnit (2 : ℤ[X]) := fun h2 ↦ by
    have h2Z : IsUnit (2 : ℤ) := by simpa using h2.map (Polynomial.evalRingHom 0)
    norm_num [Int.isUnit_iff] at h2Z
  have hnot3 : ¬ IsUnit (3 : ℤ[X]) := fun h3 ↦ by
    have h3Z : IsUnit (3 : ℤ) := by simpa using h3.map (Polynomial.evalRingHom 0)
    norm_num [Int.isUnit_iff] at h3Z
  have hne_top : Ideal.span {(2 : ℤ[X])} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  have hT2 : T2Space ℤ[X] := hI.isHausdorff_iff.mp (IsHausdorff.of_isDomain _ hne_top)
  have hnotComp : ¬ CompleteSpace ℤ[X] := by
    intro hC
    have hadicR : IsAdicComplete (Ideal.span {(2 : ℤ[X])}) ℤ[X] :=
      hI.isAdicComplete_iff.mpr ⟨hC, hT2⟩
    have h2jac : (2 : ℤ[X]) ∈ Ring.jacobson ℤ[X] :=
      IsAdicComplete.le_jacobson (Ideal.span {(2 : ℤ[X])}) (Ideal.mem_span_singleton_self 2)
    have h3unit : IsUnit (3 : ℤ[X]) := by
      have h21 : IsUnit ((2 : ℤ[X]) * 1 + 1) := Ring.mem_jacobson_iff.mp h2jac 1
      norm_num at h21
      exact h21
    exact hnot3 h3unit
  have hempty : IsEmpty (restrictedMvPowerSeriesCompletion 0 ℤ[X] ≃+* ℤ[X]) := by
    refine ⟨fun e ↦ ?_⟩
    have hadicC :
        IsAdicComplete
          ((Ideal.span {(2 : ℤ[X])}).map (Completion.coeRingHom : ℤ[X] →+* Completion ℤ[X]))
          (Completion ℤ[X]) :=
      hI.isAdicComplete_map_coeRingHom (Submodule.fg_span_singleton 2)
    have h2mem :
        (2 : Completion ℤ[X]) ∈
          (Ideal.span {(2 : ℤ[X])}).map (Completion.coeRingHom : ℤ[X] →+* Completion ℤ[X]) := by
      have hmem := Ideal.mem_map_of_mem (Completion.coeRingHom : ℤ[X] →+* Completion ℤ[X])
        (Ideal.mem_span_singleton_self (2 : ℤ[X]))
      rwa [map_ofNat] at hmem
    have h3unitC : IsUnit (3 : Completion ℤ[X]) := by
      have hjac := IsAdicComplete.le_jacobson _ h2mem
      have h21 : IsUnit ((2 : Completion ℤ[X]) * 1 + 1) := Ring.mem_jacobson_iff.mp hjac 1
      norm_num at h21
      exact h21
    let e0 : Completion ℤ[X] ≃+* ℤ[X] :=
      (restrictedMvPowerSeriesCompletionFinZeroEquiv (A := ℤ[X])).symm.trans e
    have h3R : IsUnit (3 : ℤ[X]) :=
      map_ofNat (e0 : Completion ℤ[X] →+* ℤ[X]) 3 ▸ h3unitC.map (e0 : Completion ℤ[X] →+* ℤ[X])
    exact hnot3 h3R
  exact ⟨inferInstance, hnotComp, hempty⟩

end ZeroVariables

/-! ### Universal property: adic base `ℤ_[p]` versus Tate field `ℚ_[p]` -/

section UniversalProperty

variable (p : ℕ) [Fact p.Prime]

-- Over `ℤ_[p]` (`IsLinearTopology`), every tuple `b : Fin k → ℤ_[p]` extends uniquely to a
-- continuous `ℤ_[p]`-algebra homomorphism out of `ℤ_[p]⟨X₁, …, Xₖ⟩`.
example (k : ℕ) (b : Fin k → ℤ_[p]) :
    ∃! ψ : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set ℤ_[p]))
        isWeightFamily_one_weight →ₐ[ℤ_[p]] ℤ_[p],
      Continuous ψ ∧ ∀ i, ψ (weightedX _ isWeightFamily_one_weight i) = b i :=
  existsUnique_continuous_algHom_weightedRestrictedSubring_of_isLinearTopology
    isWeightFamily_one_weight continuous_id.continuousAt b

-- By contrast, `ℚ_[p]` is not linearly topologized, and `X₀ ↦ p⁻¹` (`‖p⁻¹‖ = p > 1`) admits no
-- continuous ring homomorphism `ℚ_[p]⟨X₀⟩ →+* ℚ_[p]` extending `id : ℚ_[p] →+* ℚ_[p]`.
example :
    ¬ IsLinearTopology ℚ_[p] ℚ_[p] ∧
      ¬ ∃ ψ : MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ 1) →+* ℚ_[p],
        Continuous ψ ∧
          (∀ c, ψ (algebraMap ℚ_[p] _ c) = RingHom.id ℚ_[p] c) ∧
          ∀ i, ψ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X (fun _ : Fin 1 ↦ 1) i⟩ =
            (p : ℚ_[p])⁻¹ := by
  refine ⟨not_isLinearTopology_of_nontriviallyNormedField ℚ_[p], ?_⟩
  rw [exists_continuous_ringHom_isRestricted_subring_iff_norm_le_one (θ := RingHom.id ℚ_[p])
    continuous_id (fun _ : Fin 1 ↦ (p : ℚ_[p])⁻¹)]
  intro h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnorm : ‖((p : ℚ_[p])⁻¹)‖ = (p : ℝ) := by
    rw [norm_inv, _root_.Padic.norm_p, inv_inv]
  linarith [h 0]

end UniversalProperty

end TauCeti.Examples
