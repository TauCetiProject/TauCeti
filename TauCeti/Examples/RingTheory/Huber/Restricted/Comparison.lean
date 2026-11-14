/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Filtration
public import TauCeti.RingTheory.Huber.Padic.Field
public import TauCeti.RingTheory.Huber.Restricted.Comparison
public import TauCeti.RingTheory.PowerSeries.AdicComplete
public import TauCeti.RingTheory.PowerSeries.Geometric
public import TauCeti.RingTheory.PowerSeries.TateAlgebra

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
  the inverse of `1 - X` in `ℤ_[p]⟦X⟧` yet is not restricted, whereas `ℤ_[p]⟨T⟩` admits a unique
  continuous `ℤ_[p]`-algebra evaluation into `ℤ_[p]⟦X⟧` (equipped with the linear product topology)
  at *any* formal power series, including `1 + X` (whose constant term `1` prevents formal power
  series substitution). By contrast, over `ℚ_[p]`, no continuous ring homomorphism
  `ℚ_[p]⟨T⟩ →+* ℚ_[p]` extending `id` can send `T` to `p⁻¹`.
* **Zero variables (`k = 0`)**: `algebraMap : A → restrictedMvPowerSeriesCompletion 0 A` is
  bijective when `A` is complete and Hausdorff, fails to be injective on `ℤ[X]` with the indiscrete
  (`⊤`-adic) topology (complete, not separated), and fails to be surjective on `ℤ[X]` with the
  `(X)`-adic topology (separated, not complete).
-/

public section

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

/-- The quotient `ℤ_[p] ⧸ (maximalIdeal ℤ_[p]) ^ m` is isomorphic to `ZMod (p ^ m)`. -/
noncomputable def padicIntQuotientPowEquivZMod (m : ℕ) :
    (ℤ_[p] ⧸ maximalIdeal ℤ_[p] ^ m) ≃+* ZMod (p ^ m) :=
  (Ideal.quotEquivOfEq (by
      rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
        ← _root_.PadicInt.ker_toZModPow m])).trans
    ((_root_.PadicInt.toZModPow m).quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (_root_.PadicInt.toZModPow m)))

/-- For `m ≠ 0`, reducing Gauss-normed restricted power series `ℤ_[p]⟨X₁, …, Xₖ⟩` modulo `(p)ᵐ`
yields `(ℤ/pᵐℤ)[X₁, …, Xₖ]`. -/
noncomputable example (k : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1) ⧸
      (maximalIdeal ℤ_[p]).map
        (algebraMap ℤ_[p]
          (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1))) ^ m) ≃+*
      MvPolynomial (Fin k) (ZMod (p ^ m)) :=
  have hfg : (maximalIdeal ℤ_[p]).FG := by
    rw [_root_.PadicInt.maximalIdeal_eq_span_p]
    exact Submodule.fg_span_singleton _
  (quotientPowIsRestrictedEquivMvPolynomialQuotient
    PadicInt.isAdic_maximalIdeal hfg hm).toRingEquiv.trans
    (MvPolynomial.mapEquiv (Fin k) (padicIntQuotientPowEquivZMod p m))

/-- For `m ≠ 0`, reducing completed Huber restricted power series over `ℤ_[p]` modulo `(p)ᵐ`
likewise yields `(ℤ/pᵐℤ)[X₁, …, Xₖ]`. -/
noncomputable example (k : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (restrictedMvPowerSeriesCompletion k ℤ_[p] ⧸
      (maximalIdeal ℤ_[p]).map
        (algebraMap ℤ_[p] (restrictedMvPowerSeriesCompletion k ℤ_[p])) ^ m) ≃+*
      MvPolynomial (Fin k) (ZMod (p ^ m)) :=
  have hfg : (maximalIdeal ℤ_[p]).FG := by
    rw [_root_.PadicInt.maximalIdeal_eq_span_p]
    exact Submodule.fg_span_singleton _
  (quotientPowRestrictedCompletionEquivMvPolynomialQuotient
    PadicInt.isAdic_maximalIdeal hfg hm).toRingEquiv.trans
    (MvPolynomial.mapEquiv (Fin k) (padicIntQuotientPowEquivZMod p m))

/-- Gauss-normed restricted power series `ℤ_[p]⟨X₁, …, Xₖ⟩` form a noetherian ring whose Gauss-norm
topology is `(p · ℤ_[p]⟨X⟩)`-adic. -/
example (k : ℕ) :
    IsNoetherianRing (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)) ∧
      IsAdic ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p]
        (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)))) := by
  have hfg : (maximalIdeal ℤ_[p]).FG := by
    rw [_root_.PadicInt.maximalIdeal_eq_span_p]
    exact Submodule.fg_span_singleton _
  exact ⟨isNoetherianRing_isRestricted_subring_of_isAdic PadicInt.isAdic_maximalIdeal,
    isAdic_map_algebraMap_isRestricted_subring PadicInt.isAdic_maximalIdeal hfg⟩

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
      Continuous ψ ∧
        (∀ r : ℤ_[p], ψ (algebraMap ℤ_[p] _ r) = PowerSeries.C r) ∧
        ∀ i : Fin 1,
          ψ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ = 1 + PowerSeries.X := by
  let : WithIdeal (PowerSeries ℤ_[p]) := ⟨maximalIdeal (PowerSeries ℤ_[p])⟩
  have hAdic : IsAdic (maximalIdeal (PowerSeries ℤ_[p])) := rfl
  have hcomp : IsAdicComplete (maximalIdeal (PowerSeries ℤ_[p])) (PowerSeries ℤ_[p]) :=
    PowerSeries.isAdicComplete_maximalIdeal
  obtain ⟨_, _⟩ := hAdic.isAdicComplete_iff.mp hcomp
  have : IsLinearTopology (PowerSeries ℤ_[p]) (PowerSeries ℤ_[p]) := hAdic.isLinearTopology
  have hC : Continuous (PowerSeries.C : ℤ_[p] →+* PowerSeries ℤ_[p]) := by
    refine continuous_of_continuousAt_zero (PowerSeries.C : ℤ_[p] →+* PowerSeries ℤ_[p]) ?_
    rw [ContinuousAt, map_zero,
      (PadicInt.isAdic_maximalIdeal.hasBasis_nhds_zero.tendsto_iff hAdic.hasBasis_nhds_zero)]
    refine fun n _ ↦ ⟨n, trivial, fun r hr ↦ ?_⟩
    have hmap : (maximalIdeal ℤ_[p]).map PowerSeries.C ≤ maximalIdeal (PowerSeries ℤ_[p]) :=
      Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
        rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
        rw [mem_maximalIdeal, mem_nonunits_iff] at ha
        exact fun hu ↦ ha (by simpa using hu.map PowerSeries.constantCoeff)
    exact Ideal.pow_right_mono hmap n
      (Ideal.map_pow PowerSeries.C (maximalIdeal ℤ_[p]) n ▸ Ideal.mem_map_of_mem _ hr)
  exact existsUnique_continuous_ringHom_isRestricted_subring_of_isLinearTopology
    hC (fun _ ↦ 1 + PowerSeries.X)

/-- Over the Tate field `ℚ_[p]`, by contrast, there is no continuous ring homomorphism
`ℚ_[p]⟨T⟩ →+* ℚ_[p]` extending the identity on `ℚ_[p]` and sending `T` to `p⁻¹`. -/
example :
    ¬ ∃ ψ : MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) (fun _ : Fin 1 ↦ 1) →+* ℚ_[p],
      Continuous ψ ∧
        (∀ r : ℚ_[p], ψ (algebraMap ℚ_[p] _ r) = r) ∧
        ∀ i : Fin 1,
          ψ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_X _ i⟩ = (p : ℚ_[p])⁻¹ := by
  rintro ⟨ψ, hψc, hC, hX⟩
  have hle := (exists_continuous_ringHom_isRestricted_subring_iff_forall_norm_le_one
    (φ := RingHom.id ℚ_[p]) continuous_id (fun _ : Fin 1 ↦ (p : ℚ_[p])⁻¹)).mp
    ⟨ψ, hψc, hC, hX⟩ 0
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
  have hcompA : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := by
    rwa [IsUniformAddGroup.rightUniformSpace_eq]
  let e : restrictedMvPowerSeriesCompletion 0 A ≃+* A :=
    restrictedMvPowerSeriesCompletionFinZeroEquiv.trans
      (@UniformSpace.Completion.completeRingEquivSelf A _
        (IsTopologicalAddGroup.rightUniformSpace A) _
        (isUniformAddGroup_of_addCommGroup (G := A)) hcompA _)
  have hcomp : ∀ a : A, e (algebraMap A (restrictedMvPowerSeriesCompletion 0 A) a) = a := by
    intro a
    rw [RingEquiv.trans_apply, algebraMap_completion_weightedRestrictedSubring_apply,
      restrictedMvPowerSeriesCompletionFinZeroEquiv_coe]
    have hw : weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A))
        (weightedC _ isWeightFamily_one_weight a) = a := by
      rw [weightedRestrictedSubringFinZeroEquiv_apply, coe_weightedC, MvPowerSeries.constantCoeff_C]
    rw [hw]
    exact @UniformSpace.Completion.completeRingEquivSelf_coe A _
      (IsTopologicalAddGroup.rightUniformSpace A) _
      (isUniformAddGroup_of_addCommGroup (G := A)) hcompA _ a
  exact ⟨Function.LeftInverse.injective hcomp,
    fun x ↦ ⟨e x, e.injective (hcomp (e x))⟩⟩

/-- When `ℤ[X]` carries the indiscrete (`⊤`-adic) topology — which is complete and nonarchimedean
but not separated — `algebraMap : ℤ[X] →+* restrictedMvPowerSeriesCompletion 0 ℤ[X]` is not
injective. -/
example :
    letI : WithIdeal ℤ[X] := ⟨⊤⟩
    CompleteSpace ℤ[X] ∧
      ¬ Function.Injective (algebraMap ℤ[X] (restrictedMvPowerSeriesCompletion 0 ℤ[X])) := by
  let : WithIdeal ℤ[X] := ⟨⊤⟩
  have hAdic : IsAdic (⊤ : Ideal ℤ[X]) := rfl
  have hfg : (⊤ : Ideal ℤ[X]).FG := ⟨{1}, by simp⟩
  have hpre : IsPrecomplete (⊤ : Ideal ℤ[X]) ℤ[X] :=
    ⟨fun _ _ ↦ ⟨0, fun n ↦ by simp [SModEq.zero, Submodule.eq_top_iff'.mp (Ideal.top_pow _ n)]⟩⟩
  refine ⟨hAdic.isPrecomplete_iff.mp hpre, fun hinj ↦ ?_⟩
  let S := weightedRestrictedSubring (fun _ : Fin 0 ↦ ({1} : Set ℤ[X])) isWeightFamily_one_weight
  let e := restrictedMvPowerSeriesCompletionEquivAdicCompletion (k := 0) hAdic hfg
  have hsub : Subsingleton (AdicCompletion ((⊤ : Ideal ℤ[X]).map (algebraMap ℤ[X] S)) S) := by
    refine ⟨fun x y ↦ AdicCompletion.ext fun n ↦ ?_⟩
    have htop : (((⊤ : Ideal ℤ[X]).map (algebraMap ℤ[X] S)) ^ n • (⊤ : Submodule S S)) = ⊤ := by
      rw [Ideal.map_top, Ideal.top_pow, smul_eq_mul, Ideal.top_mul]
    have : Subsingleton _ := Submodule.Quotient.subsingleton_iff.mpr htop
    exact Subsingleton.elim _ _
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
  have hfg : I.FG := Submodule.fg_span_singleton Polynomial.X
  have hI_ne_top : I ≠ ⊤ := Ideal.span_singleton_ne_top Polynomial.not_isUnit_X
  have hiInf : ⨅ n : ℕ, I ^ n = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain I hI_ne_top
  have hHaus : IsHausdorff I ℤ[X] := by
    rw [isHausdorff_iff]
    intro f hf
    have hf' : f ∈ ⨅ n : ℕ, I ^ n := by
      rw [Submodule.mem_iInf]
      intro n
      simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hf n
    rwa [hiInf, Submodule.mem_bot] at hf'
  refine ⟨hAdic.isHausdorff_iff.mp hHaus, fun hsurj ↦ ?_⟩
  let e : restrictedMvPowerSeriesCompletion 0 ℤ[X] ≃+* AdicCompletion I ℤ[X] :=
    restrictedMvPowerSeriesCompletionFinZeroEquiv.trans
      (hAdic.completionEquivAdicCompletion hfg)
  have he : ∀ f : ℤ[X], e (algebraMap ℤ[X] (restrictedMvPowerSeriesCompletion 0 ℤ[X]) f) =
      algebraMap ℤ[X] (AdicCompletion I ℤ[X]) f := by
    intro f
    rw [RingEquiv.trans_apply, algebraMap_completion_weightedRestrictedSubring_apply,
      restrictedMvPowerSeriesCompletionFinZeroEquiv_coe]
    have hw : weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set ℤ[X]))
        (weightedC _ isWeightFamily_one_weight f) = f := by
      rw [weightedRestrictedSubringFinZeroEquiv_apply, coe_weightedC, MvPowerSeries.constantCoeff_C]
    rw [hw, IsAdic.completionEquivAdicCompletion_coe hAdic hfg f]
  have hcomp : IsAdicComplete (I.map (algebraMap ℤ[X] (AdicCompletion I ℤ[X])))
      (AdicCompletion I ℤ[X]) :=
    (IsAdicComplete.map_algebraMap_iff I _).mpr (AdicCompletion.isAdicComplete hfg)
  have hX_jac : algebraMap ℤ[X] (AdicCompletion I ℤ[X]) Polynomial.X ∈
      Ring.jacobson (AdicCompletion I ℤ[X]) :=
    IsAdicComplete.le_jacobson _
      (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self Polynomial.X))
  have hunit : IsUnit (1 + algebraMap ℤ[X] (AdicCompletion I ℤ[X]) Polynomial.X) := by
    rw [add_comm]
    simpa using Ring.mem_jacobson_iff.mp hX_jac 1
  obtain ⟨u, hu⟩ := hunit
  obtain ⟨x, hx⟩ := e.surjective ↑u⁻¹
  obtain ⟨g, rfl⟩ := hsurj x
  have hg1 : algebraMap ℤ[X] (AdicCompletion I ℤ[X]) ((1 + Polynomial.X) * g - 1) = 0 := by
    rw [map_sub, map_mul, map_add, map_one, ← he g, hx, ← hu, Units.mul_inv, sub_self]
  have hg_mem : (1 + Polynomial.X) * g - 1 ∈ ⨅ n : ℕ, I ^ n := by
    rw [Submodule.mem_iInf]
    intro n
    have h0 := congrArg (AdicCompletion.evalₐ I n) hg1
    rw [map_zero, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of,
      Ideal.Quotient.eq_zero_iff_mem] at h0
    simpa using h0
  rw [hiInf, Submodule.mem_bot, sub_eq_zero] at hg_mem
  have hunitPoly : IsUnit (1 + (Polynomial.X : ℤ[X])) := IsUnit.of_mul_eq_one g hg_mem
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hunitPoly
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff := congrArg (fun p : ℤ[X] ↦ p.coeff 1) hC
  simp at hcoeff

end ZeroVariables

end TauCeti.Examples
