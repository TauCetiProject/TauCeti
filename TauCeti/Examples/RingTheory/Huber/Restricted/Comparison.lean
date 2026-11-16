/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Filtration
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Huber.Padic.Basic
import TauCeti.RingTheory.Huber.Restricted.Comparison
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Geometric
import TauCeti.RingTheory.PowerSeries.Restricted

/-!
# Examples of restricted power series over adic, discrete, and `p`-adic rings

Concrete tests of the adic quotient presentations, noetherianity, Gauss comparison, universal
properties into linearly topologized and normed targets, and zero-variable boundary behavior of
restricted power series:

* **Discrete coefficients**: when the base ring carries the discrete topology, both the uncompleted
  and completed restricted-series algebras (and the Gauss-normed restricted-series ring) coincide
  with the polynomial ring `A[X₁, …, Xₖ]`.
* **`p`-adic integers `ℤ_[p]`**: for prime `p` and `m ≠ 0`, both the Gauss-normed quotient
  `ℤ_[p]⟨X₁, …, Xₖ⟩ ⧸ (p · ℤ_[p]⟨X⟩)ᵐ` and the completed Huber quotient are isomorphic to
  `(ℤ/pᵐℤ)[X₁, …, Xₖ]`, and `ℤ_[p]⟨X₁, …, Xₖ⟩` is noetherian with `(p)`-adic Gauss topology.
* **Formal vs. restricted power series and linear vs. field evaluation**: over `ℤ_[p]`, `∑ Xⁿ` is
  the inverse of `1 - X` in `ℤ_[p]⟦X⟧` yet is not restricted, whereas equipping `ℤ_[p]⟦X⟧` with its
  `(p, X)`-adic maximal-ideal topology yields a unique continuous ring homomorphism
  `ℤ_[p]⟨T⟩ →+* ℤ_[p]⟦X⟧` extending `PowerSeries.C` and sending `T` to `1 + X` (whose constant
  term `1` prevents formal power series substitution). By contrast, over `ℚ_[p]`, no continuous
  ring homomorphism `ℚ_[p]⟨T⟩ →+* ℚ_[p]` extending `id` can send `T` to `p⁻¹`.
* **Zero variables (`k = 0`)**: `algebraMap : A → restrictedMvPowerSeriesCompletion 0 A` is
  bijective when `A` is complete and Hausdorff, fails to be injective on `ℤ[X]` with the indiscrete
  (`⊤`-adic) topology (complete, not separated), and fails to be surjective on `ℤ[X]` with the
  `(X)`-adic topology (separated, not complete).
-/

open Filter Topology TauCeti.Huber TauCeti.MvPowerSeries IsLocalRing Polynomial

namespace TauCeti.Examples

/-! ### Discrete base rings -/

section Discrete

/-- Over a discrete base ring `A`, the uncompleted restricted-series subring is isomorphic to the
polynomial ring `A[X₁, …, Xₖ]`. -/
noncomputable example (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [DiscreteTopology A] :
    MvPolynomial (Fin k) A ≃+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight

/-- Over a discrete uniform base ring `A`, the completed restricted-series algebra is also
isomorphic to `A[X₁, …, Xₖ]`. -/
noncomputable example (k : ℕ) (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [NonarchimedeanRing A] [DiscreteTopology A] :
    MvPolynomial (Fin k) A ≃+* restrictedMvPowerSeriesCompletion k A :=
  let _ : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let _ : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  let _ : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  (weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).trans
    (restrictedMvPowerSeriesCompletionEquiv k A).symm

/-- Over a discretely normed ultrametric commutative ring `R`, the Gauss-normed restricted-series
ring `R⟨X₁, …, Xₖ⟩` coincides with `R[X₁, …, Xₖ]`. -/
noncomputable example (k : ℕ) (R : Type*) [NormedCommRing R] [IsUltrametricDist R]
    [DiscreteTopology R] :
    MvPolynomial (Fin k) R ≃+* MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
  (weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).trans
    restrictedMvPowerSeriesGaussEquiv

end Discrete

/-! ### Restricted power series over `ℤ_[p]` -/

section PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- For `m ≠ 0`, reducing Gauss-normed restricted power series `ℤ_[p]⟨X₁, …, Xₖ⟩` modulo `(p)ᵐ`
yields `(ℤ/pᵐℤ)[X₁, …, Xₖ]`. -/
noncomputable example (k : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1) ⧸
      (maximalIdeal ℤ_[p]).map
        (algebraMap ℤ_[p] (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1))) ^
          m) ≃+* MvPolynomial (Fin k) (ZMod (p ^ m)) :=
  (quotientPowIsRestrictedEquivMvPolynomialQuotient PadicInt.isAdic_maximalIdeal
    (IsNoetherian.noetherian _) hm).toRingEquiv.trans
    (MvPolynomial.mapEquiv (Fin k) ((Ideal.quotEquivOfEq (by
      rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow])).trans
      (_root_.PadicInt.quotientSpanPowEquivZMod m)))

/-- For `m ≠ 0`, reducing completed Huber restricted power series over `ℤ_[p]` modulo `(p)ᵐ`
likewise yields `(ℤ/pᵐℤ)[X₁, …, Xₖ]`. -/
noncomputable example (k : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (restrictedMvPowerSeriesCompletion k ℤ_[p] ⧸
      (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (restrictedMvPowerSeriesCompletion k ℤ_[p])) ^ m)
      ≃+* MvPolynomial (Fin k) (ZMod (p ^ m)) :=
  (quotientPowRestrictedCompletionEquivMvPolynomialQuotient PadicInt.isAdic_maximalIdeal
    (IsNoetherian.noetherian _) hm).toRingEquiv.trans
    (MvPolynomial.mapEquiv (Fin k) ((Ideal.quotEquivOfEq (by
      rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow])).trans
      (_root_.PadicInt.quotientSpanPowEquivZMod m)))

/-- Gauss-normed restricted power series `ℤ_[p]⟨X₁, …, Xₖ⟩` form a noetherian ring whose Gauss-norm
topology is `(p · ℤ_[p]⟨X⟩)`-adic. -/
example (k : ℕ) :
    IsNoetherianRing (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)) ∧
      IsAdic ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p]
        (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)))) :=
  ⟨isNoetherianRing_isRestricted_subring_of_isAdic PadicInt.isAdic_maximalIdeal,
   isAdic_map_algebraMap_isRestricted_subring PadicInt.isAdic_maximalIdeal
     (IsNoetherian.noetherian _)⟩

end PadicInt

/-! ### Formal vs. restricted series and linear vs. field evaluation -/

section FormalVsRestricted

variable (p : ℕ) [hp : Fact p.Prime]

/-- Over `ℤ_[p]`, the geometric series `∑ Xⁿ` inverts `1 - X` inside `ℤ_[p]⟦X⟧` yet is not a
unit-radius restricted power series. -/
example :
    (PowerSeries.mk (1 : ℕ → ℤ_[p])) * (1 - PowerSeries.X) = 1 ∧
      ¬ (PowerSeries.mk (1 : ℕ → ℤ_[p])).IsRestricted 1 :=
  ⟨by rw [Pi.one_def]; simpa using powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (1 : ℤ_[p]),
   PowerSeries.not_isRestricted_mk_one⟩

/-- Even though `1 + X ∈ ℤ_[p]⟦X⟧` has unit constant term `1` (so formal power series in
`ℤ_[p]⟦T⟧` cannot be evaluated at `1 + X`), equipping the Iwasawa algebra `ℤ_[p]⟦X⟧` with its
`(p, X)`-adic maximal-ideal topology makes it a complete Hausdorff linearly topologized ring, and
therefore yields a unique continuous ring homomorphism `ℤ_[p]⟨T⟩ →+* ℤ_[p]⟦X⟧` extending
`PowerSeries.C` and sending `T` to `1 + X`. -/
example :
    letI : WithIdeal (PowerSeries ℤ_[p]) := ⟨maximalIdeal (PowerSeries ℤ_[p])⟩
    ∃! ψ : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) →+*
        PowerSeries ℤ_[p],
      Continuous ψ ∧ (∀ r : ℤ_[p], ψ (algebraMap ℤ_[p] _ r) = PowerSeries.C r) ∧
        ∀ i : Fin 1,
          ψ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ = 1 + PowerSeries.X := by
  let : WithIdeal (PowerSeries ℤ_[p]) := ⟨maximalIdeal (PowerSeries ℤ_[p])⟩
  have hAdic : IsAdic (maximalIdeal (PowerSeries ℤ_[p])) := rfl
  obtain ⟨_, _⟩ := hAdic.isAdicComplete_iff.mp PowerSeries.isAdicComplete_maximalIdeal
  have : IsLinearTopology (PowerSeries ℤ_[p]) (PowerSeries ℤ_[p]) := hAdic.isLinearTopology
  have hmap : (maximalIdeal ℤ_[p]).map PowerSeries.C ≤ maximalIdeal (PowerSeries ℤ_[p]) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rw [mem_maximalIdeal, mem_nonunits_iff] at ha
      exact fun hu ↦ ha (by simpa using hu.map PowerSeries.constantCoeff)
  exact existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology
    (PadicInt.isAdic_maximalIdeal.continuous_of_map_le_radical hAdic (IsNoetherian.noetherian _)
      (hmap.trans Ideal.le_radical)) fun _ ↦ 1 + PowerSeries.X

/-- Over the Tate field `ℚ_[p]`, by contrast, there is no continuous ring homomorphism
`ℚ_[p]⟨T⟩ →+* ℚ_[p]` extending the identity on `ℚ_[p]` and sending `T` to `p⁻¹`. -/
example :
    ¬ ∃ ψ : MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ 1) →+* ℚ_[p],
      Continuous ψ ∧ (∀ r : ℚ_[p], ψ (algebraMap ℚ_[p] _ r) = r) ∧
        ∀ i : Fin 1, ψ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ = (p : ℚ_[p])⁻¹ := by
  rintro ⟨ψ, hψc, hC, hX⟩
  have hle := (exists_continuous_ringHom_isRestricted_subring_iff_forall_norm_le_one
    (φ := RingHom.id ℚ_[p]) continuous_id (fun _ : Fin 1 ↦ (p : ℚ_[p])⁻¹)).mp ⟨ψ, hψc, hC, hX⟩ 0
  rw [norm_inv, Padic.norm_p, inv_inv] at hle
  exact not_le_of_gt (mod_cast hp.out.one_lt) hle

end FormalVsRestricted

/-! ### Zero variables (`k = 0`) -/

section ZeroVariables

/-- When `A` is complete and separated (`T0Space`), the constant-series map
`A →+* restrictedMvPowerSeriesCompletion 0 A` is bijective. -/
example (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
    [CompleteSpace A] [T0Space A] :
    Function.Bijective (algebraMap A (restrictedMvPowerSeriesCompletion 0 A)) := by
  let e : restrictedMvPowerSeriesCompletion 0 A ≃+* A :=
    (restrictedMvPowerSeriesCompletionEquiv 0 A).trans
      (weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A)))
  have hcomp : ∀ a : A, e (algebraMap A (restrictedMvPowerSeriesCompletion 0 A) a) = a :=
    fun a ↦ by simp [e]
  exact ⟨Function.LeftInverse.injective hcomp, fun x ↦ ⟨e x, e.injective (hcomp (e x))⟩⟩

/-- When `ℤ[X]` carries the indiscrete (`⊤`-adic) topology — which is complete and nonarchimedean
but not separated — `algebraMap : ℤ[X] →+* restrictedMvPowerSeriesCompletion 0 ℤ[X]` is not
injective. -/
example :
    letI : WithIdeal ℤ[X] := ⟨⊤⟩
    CompleteSpace ℤ[X] ∧
      ¬ Function.Injective (algebraMap ℤ[X] (restrictedMvPowerSeriesCompletion 0 ℤ[X])) := by
  let : WithIdeal ℤ[X] := ⟨⊤⟩
  have hAdic : IsAdic (⊤ : Ideal ℤ[X]) := rfl
  have hpre : IsPrecomplete (⊤ : Ideal ℤ[X]) ℤ[X] :=
    ⟨fun _ _ ↦ ⟨0, fun n ↦ by simp [SModEq.zero, Submodule.eq_top_iff'.mp (Ideal.top_pow _ n)]⟩⟩
  refine ⟨hAdic.isPrecomplete_iff.mp hpre, fun hinj ↦ ?_⟩
  let P := MvPolynomial (Fin 0) ℤ[X]
  let e := restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := 0) hAdic ⟨{1}, by simp⟩
  have : Subsingleton (AdicCompletion ((⊤ : Ideal ℤ[X]).map (MvPolynomial.C : ℤ[X] →+* P)) P) :=
    ⟨fun _ _ ↦ AdicCompletion.ext fun n ↦ @Subsingleton.elim _
      (Submodule.Quotient.subsingleton_iff.mpr
        (by rw [Ideal.map_top, Ideal.top_pow, smul_eq_mul, Ideal.top_mul])) _ _⟩
  exact one_ne_zero (hinj (e.injective (Subsingleton.elim _ _)))

/-- When `ℤ[X]` carries the `(X)`-adic topology — which is Hausdorff (`T2Space`) and
nonarchimedean but not complete — `algebraMap : ℤ[X] →+* restrictedMvPowerSeriesCompletion 0 ℤ[X]`
is not surjective. -/
example :
    letI : WithIdeal ℤ[X] := ⟨Ideal.span {Polynomial.X}⟩
    T2Space ℤ[X] ∧
      ¬ Function.Surjective (algebraMap ℤ[X] (restrictedMvPowerSeriesCompletion 0 ℤ[X])) := by
  let I : Ideal ℤ[X] := Ideal.span {Polynomial.X}
  let : WithIdeal ℤ[X] := ⟨I⟩
  have hAdic : IsAdic I := rfl
  -- `ℤ[X]` is `(X)`-adically separated because `⨅ n, (X)^n = ⊥` in the domain `ℤ[X]`.
  have hHaus : IsHausdorff I ℤ[X] := isHausdorff_iff.mpr fun f hf ↦ by
    have hf' : f ∈ ⨅ n : ℕ, I ^ n := by
      rw [Submodule.mem_iInf]
      exact fun n ↦ by simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hf n
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain I
      (Ideal.span_singleton_ne_top Polynomial.not_isUnit_X), Submodule.mem_bot] at hf'
  refine ⟨hAdic.isHausdorff_iff.mp hHaus, fun hsurj ↦ ?_⟩
  -- Transport surjectivity of `algebraMap` to surjectivity of `AdicCompletion.of I ℤ[X]`.
  have hfg : I.FG := Submodule.fg_span_singleton Polynomial.X
  let e : restrictedMvPowerSeriesCompletion 0 ℤ[X] ≃+* AdicCompletion I ℤ[X] :=
    restrictedMvPowerSeriesCompletionFinZeroEquiv.trans (hAdic.completionEquivAdicCompletion hfg)
  have he : ∀ f : ℤ[X], e (algebraMap ℤ[X] (restrictedMvPowerSeriesCompletion 0 ℤ[X]) f) =
      AdicCompletion.of I ℤ[X] f := fun f ↦ by simp [e, AdicCompletion.algebraMap_apply]
  have hsurj_of : Function.Surjective (AdicCompletion.of I ℤ[X]) := fun y ↦ by
    obtain ⟨f, hf⟩ := hsurj (e.symm y)
    exact ⟨f, by rw [← he f, hf, e.apply_symm_apply]⟩
  -- Bijectivity of `AdicCompletion.of` would make `ℤ[X]` `(X)`-adically complete, forcing `1 + X`
  -- to be a polynomial unit.
  have : IsAdicComplete I ℤ[X] := AdicCompletion.of_bijective_iff.mp
    ⟨by have := hHaus; exact AdicCompletion.of_injective I ℤ[X], hsurj_of⟩
  have hunit : IsUnit (1 + (Polynomial.X : ℤ[X])) := by
    rw [add_comm]
    simpa using Ring.mem_jacobson_iff.mp
      (IsAdicComplete.le_jacobson I (Ideal.mem_span_singleton_self Polynomial.X)) 1
  have hC := congrArg (fun p : ℤ[X] ↦ p.coeff 1)
    (Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hunit))
  simp at hC

end ZeroVariables

end TauCeti.Examples
