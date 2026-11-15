/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Adic
public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Huber.Restricted.OneVariable
import TauCeti.RingTheory.PowerSeries.Restricted
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FinCases

/-!
# Examples and boundary checks for adic restricted power series

These examples exercise the restricted power-series theory across four regimes:

1. **Discrete coefficients**: over a discrete commutative ring `A`, both the restricted-series
   subring and its separated completion `A⟨X₁, …, Xₖ⟩` coincide with the polynomial algebra
   `A[X₁, …, Xₖ]`.
2. **`p`-adic integers `ℤ_[p]`**: both the completed Huber algebra and the Gauss-normed unit-radius
   subring over `ℤ_[p]` are adic noetherian rings, and their quotients modulo `(p)ᵐ` are
   canonically isomorphic to `(ℤ / pᵐℤ)[X₁, …, Xₖ]` for every `m : ℕ`.
3. **Formal versus restricted power series**: the geometric series `∑ₙ Xⁿ` lies in `ℤ_[p]⟦X⟧`
   (`PowerSeries ℤ_[p]`) and `MvPowerSeries (Fin 1) ℤ_[p]`, and lies outside `ℤ_[p]⟨X⟩` on both the
   Gauss-normed and Huber carriers because its coefficients are identically `1`.
4. **Zero-variable completion `A⟨⟩`**: `restrictedMvPowerSeriesCompletion 0 A` is the separated
   completion of `A`, isomorphic to `A` when `A` is complete and Hausdorff, and genuinely distinct
   from `A` both when `A` fails to be Hausdorff (`(ZMod 2)[T]` with the indiscrete topology) and
   when `A` is Hausdorff yet incomplete (`(ZMod 2)[T]` with the `(T)`-adic topology).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

namespace TauCeti.Examples.Restricted

open Topology UniformSpace TauCeti.Huber TauCeti.MvPowerSeries

section Discrete

/-- Over a discrete commutative ring `A`, the restricted-series subring is isomorphic to the
polynomial ring `MvPolynomial (Fin k) A`. -/
noncomputable example (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ≃+*
      MvPolynomial (Fin k) A :=
  (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set A))
    isWeightFamily_one_weight).symm

/-- Over a discrete commutative ring `A`, the completed restricted-series algebra `A⟨X₁, …, Xₖ⟩`
is also isomorphic to `MvPolynomial (Fin k) A`. -/
noncomputable example (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    restrictedMvPowerSeriesCompletion k A ≃+* MvPolynomial (Fin k) A :=
  (restrictedMvPowerSeriesCompletionEquiv k A).trans
    (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight).symm

end Discrete

section PadicInt

variable (p : ℕ) [Fact p.Prime] (k : ℕ)

/-- Over `ℤ_[p]`, both the completed Huber restricted-series algebra and the Gauss-normed
unit-radius restricted-series subring are adic noetherian rings. -/
example :
    IsAdicRing (restrictedMvPowerSeriesCompletion k ℤ_[p]) ∧
      IsNoetherianRing (restrictedMvPowerSeriesCompletion k ℤ_[p]) ∧
      IsAdicRing (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) fun _ : Fin k ↦ 1) ∧
      IsNoetherianRing (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) fun _ : Fin k ↦ 1) ∧
      IsStronglyNoetherian (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) fun _ : Fin k ↦ 1) :=
  ⟨inferInstance,
    isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k PadicInt.isAdic_span_p,
    inferInstance,
    isNoetherianRing_isRestricted_subring_of_isAdic PadicInt.isAdic_span_p,
    inferInstance⟩

/-- Modulo `(p)ᵐ`, the completed Huber algebra `ℤ_[p]⟨X₁, …, Xₖ⟩` is isomorphic to
`MvPolynomial (Fin k) (ZMod (p ^ m))` for every `m : ℕ`. -/
noncomputable example (m : ℕ) :
    (restrictedMvPowerSeriesCompletion k ℤ_[p] ⧸
      ((Ideal.span {(p : ℤ_[p])}).map
        (algebraMap ℤ_[p] (restrictedMvPowerSeriesCompletion k ℤ_[p]))) ^ m) ≃+*
      MvPolynomial (Fin k) (ZMod (p ^ m)) :=
  (quotientRestrictedCompletionPowEquivMvPolynomialQuotient PadicInt.isAdic_span_p
    (Submodule.fg_span_singleton _) m).toRingEquiv.trans
      (MvPolynomial.mapEquiv (Fin k) ((Ideal.quotEquivOfEq (Ideal.span_singleton_pow _ m)).trans
        (_root_.PadicInt.quotientSpanPowEquivZMod m)))

/-- Modulo `(p)ᵐ`, the Gauss-normed subring `ℤ_[p]⟨X₁, …, Xₖ⟩` is likewise isomorphic to
`MvPolynomial (Fin k) (ZMod (p ^ m))` for every `m : ℕ`. -/
noncomputable example (m : ℕ) :
    (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1) ⧸
      ((Ideal.span {(p : ℤ_[p])}).map
        (algebraMap ℤ_[p]
          (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)))) ^ m) ≃+*
      MvPolynomial (Fin k) (ZMod (p ^ m)) :=
  (quotientIsRestrictedSubringPowEquivMvPolynomialQuotient PadicInt.isAdic_span_p
    (Submodule.fg_span_singleton _) m).toRingEquiv.trans
      (MvPolynomial.mapEquiv (Fin k) ((Ideal.quotEquivOfEq (Ideal.span_singleton_pow _ m)).trans
        (_root_.PadicInt.quotientSpanPowEquivZMod m)))

/-- Evaluating a restricted series over `ℤ_[p]` at any tuple `b : Fin k → ℤ_[p]` (via
`restrictedLiftOfIsLinearTopology`, with no norm bound needed because `ℤ_[p]` is linearly
topologised) and reducing modulo `(p)ᵐ` evaluates the polynomial reduction modulo `(p)ᵐ`. -/
example (m : ℕ) (b : Fin k → ℤ_[p])
    (f : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)) :
    let hopen := (PadicInt.isAdic_span_p (p := p)).isOpen_pow m
    Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])} ^ m)
        (restrictedLiftOfIsLinearTopology (φ := RingHom.id ℤ_[p]) continuous_id b f) =
      MvPolynomial.eval₂ (Ideal.quotientMap _ (RingHom.id ℤ_[p]) le_rfl)
        (fun i ↦ Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])} ^ m) (b i))
        ((Ideal.span {(p : ℤ_[p])} ^ m).isRestrictedSubringReduction hopen f) := by
  intro hopen
  exact mk_restrictedLiftOfIsLinearTopology continuous_id b hopen _ hopen le_rfl f

open scoped NormedField Valued in
/-- Over the valuation ring `𝒪[ℚ_[p]]`, open-ideal reduction modulo the maximal ideal agrees with
unit-ball `restrictedReduction` across `restrictedIntegerEquiv`. -/
example (f : MvPowerSeries.IsRestricted.subring (R := 𝒪[ℚ_[p]]) (fun _ : Fin k ↦ 1)) :
    (IsLocalRing.maximalIdeal 𝒪[ℚ_[p]]).isRestrictedSubringReduction
        Valued.integer.isOpen_maximalIdeal f =
      TauCeti.MvPowerSeries.restrictedReduction (restrictedIntegerEquiv f) :=
  isRestrictedSubringReduction_maximalIdeal_eq_restrictedReduction _ f

end PadicInt

section GeometricSeries

variable (p : ℕ) [Fact p.Prime]

/-- The geometric series `∑ₙ Xⁿ` exists in `ℤ_[p]⟦X⟧` (`PowerSeries ℤ_[p]`) with every coefficient
equal to `1`, while the corresponding one-variable series in `MvPowerSeries (Fin 1) ℤ_[p]` lies
outside both the Gauss-normed and Huber restricted-series subrings `ℤ_[p]⟨X⟩`. -/
example :
    let geom : MvPowerSeries (Fin 1) ℤ_[p] := fun _ ↦ 1
    (∀ n : ℕ, PowerSeries.coeff n (PowerSeries.mk (1 : ℕ → ℤ_[p])) = 1) ∧
      geom ∉ MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) ∧
      geom ∉ restrictedMvPowerSeriesSubring 1 ℤ_[p] := by
  intro geom
  have hren : MvPowerSeries.renameEquiv ℤ_[p] finOneEquiv geom = PowerSeries.mk 1 :=
    PowerSeries.ext fun n ↦
      (PowerSeries.coeff_rename finOneEquiv geom n).trans (PowerSeries.coeff_mk n 1).symm
  have hnotH : geom ∉ restrictedMvPowerSeriesSubring 1 ℤ_[p] := by
    rw [mem_restrictedMvPowerSeriesSubring, isRestricted_renameEquiv_finOne_iff, hren]
    exact TauCeti.PowerSeries.not_isRestricted_mk_one
  exact ⟨fun n ↦ PowerSeries.coeff_mk n 1,
    fun hmem ↦ hnotH (mem_restrictedMvPowerSeriesSubring.mpr
      (isRestricted_iff_isRestricted_one.mpr hmem)),
    hnotH⟩

end GeometricSeries

section ZeroVariables

/-- In zero variables, `restrictedMvPowerSeriesCompletion 0 A` is isomorphic to the separated
completion `UniformSpace.Completion A` for the canonical additive-group uniformity. -/
noncomputable example (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    restrictedMvPowerSeriesCompletion 0 A ≃+* Completion A :=
  restrictedMvPowerSeriesCompletionFinZeroEquiv

/-- When `A` is complete and Hausdorff, `restrictedMvPowerSeriesCompletion 0 A` is isomorphic as an
`A`-algebra to `A` itself. -/
noncomputable example (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [NonarchimedeanRing A] [CompleteSpace A] [T2Space A] :
    restrictedMvPowerSeriesCompletion 0 A ≃ₐ[A] A :=
  restrictedMvPowerSeriesCompletionFinZeroAlgEquiv A

/-- **Failure without separatedness**: for `(ZMod 2)[T]` equipped with the indiscrete `(⊤)`-adic
topology, `(ZMod 2)[T]` is nontrivial whereas `restrictedMvPowerSeriesCompletion 0 (ZMod 2)[T]` is
subsingleton, so the two rings are not isomorphic. -/
example :
    letI : WithIdeal (Polynomial (ZMod 2)) := ⟨⊤⟩
    Nontrivial (Polynomial (ZMod 2)) ∧
      Subsingleton (restrictedMvPowerSeriesCompletion 0 (Polynomial (ZMod 2))) ∧
      IsEmpty (restrictedMvPowerSeriesCompletion 0 (Polynomial (ZMod 2)) ≃+*
        Polynomial (ZMod 2)) := by
  let _ : WithIdeal (Polynomial (ZMod 2)) := ⟨⊤⟩
  have hI : IsAdic (⊤ : Ideal (Polynomial (ZMod 2))) := rfl
  have hcomp : IsAdicComplete
      (⊤ : Ideal (restrictedMvPowerSeriesCompletion 0 (Polynomial (ZMod 2))))
      (restrictedMvPowerSeriesCompletion 0 (Polynomial (ZMod 2))) :=
    Ideal.map_top
      (algebraMap (Polynomial (ZMod 2))
        (restrictedMvPowerSeriesCompletion 0 (Polynomial (ZMod 2)))) ▸
      isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion 0 hI ⟨{1}, by simp⟩
  have hsub := hcomp.toIsHausdorff.subsingleton
  exact ⟨inferInstance, hsub,
    ⟨fun e ↦ not_subsingleton (Polynomial (ZMod 2)) e.symm.injective.subsingleton⟩⟩

/-- **Failure without completeness**: for `(ZMod 2)[T]` equipped with the `(T)`-adic topology,
`(ZMod 2)[T]` is Hausdorff, yet `restrictedMvPowerSeriesCompletion 0 (ZMod 2)[T]` is not isomorphic
to `(ZMod 2)[T]` even as an abstract ring. -/
example :
    letI : WithIdeal (Polynomial (ZMod 2)) := ⟨Ideal.span {Polynomial.X}⟩
    T2Space (Polynomial (ZMod 2)) ∧
      IsEmpty (restrictedMvPowerSeriesCompletion 0 (Polynomial (ZMod 2)) ≃+*
        Polynomial (ZMod 2)) := by
  let _ : WithIdeal (Polynomial (ZMod 2)) := ⟨Ideal.span {Polynomial.X}⟩
  have hI : IsAdic (Ideal.span {(Polynomial.X : Polynomial (ZMod 2))}) := rfl
  have hhaus : IsHausdorff (Ideal.span {(Polynomial.X : Polynomial (ZMod 2))})
      (Polynomial (ZMod 2)) :=
    .of_isDomain _ (Ideal.span_singleton_ne_top Polynomial.not_isUnit_X)
  refine ⟨hI.isHausdorff_iff.mp hhaus, ⟨fun e ↦ ?_⟩⟩
  let S := restrictedMvPowerSeriesCompletion 0 (Polynomial (ZMod 2))
  let J := (Ideal.span {(Polynomial.X : Polynomial (ZMod 2))}).map (algebraMap _ S)
  have : IsAdicComplete J S :=
    isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion 0 hI
      (Submodule.fg_span_singleton _)
  let t : S := algebraMap (Polynomial (ZMod 2)) S Polynomial.X
  have htJ : t ∈ J := Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  have hunitS : IsUnit (t + 1) := by
    simpa using (Ring.mem_jacobson_iff.mp (IsAdicComplete.le_jacobson J htJ)) 1
  have hunitP : IsUnit (e (t + 1)) := hunitS.map e.toRingHom
  obtain ⟨c, hc, hce⟩ := Polynomial.isUnit_iff.mp hunitP
  have hc1 : c = 1 := by
    fin_cases c
    · exact absurd hc not_isUnit_zero
    · rfl
  have he1 : e (t + 1) = e 1 := by rw [← hce, hc1, map_one, map_one]
  have ht0 : t = 0 := by simpa using e.injective he1
  have hmk0 : Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial (ZMod 2))} ^ 2)
      Polynomial.X = 0 := by
    have h := congrArg
      (((Ideal.span {(Polynomial.X : Polynomial (ZMod 2))}) ^ 2).restrictedReductionCompletion
        (k := 0) (hI.isOpen_pow 2)) ht0
    simp only [t, S, map_zero, Ideal.restrictedReductionCompletion_algebraMap] at h
    exact MvPolynomial.C_injective (Fin 0) _ (by simpa using h)
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmk0
  have hdeg := Polynomial.natDegree_le_of_dvd hmk0 Polynomial.X_ne_zero
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at hdeg
  omega

end ZeroVariables

end TauCeti.Examples.Restricted

end
