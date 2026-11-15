/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.MvPowerSeries.LinearTopology
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.Huber.Restricted.Comparison
public import TauCeti.RingTheory.PowerSeries.TateAlgebra
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Examples of restricted power series over adic rings

These examples exercise the Huber and Gauss-normed restricted power-series algebras, their
polynomial reductions, inverse-limit cones, and linear-topology evaluation over discrete bases,
`ℤ_[p]`, and incomplete or non-Hausdorff coefficient rings.

* Over a discrete commutative ring `A`, both `restrictedMvPowerSeriesCompletion k A` and
  `MvPowerSeries.IsRestricted.subring (fun _ : Fin k ↦ 1)` collapse to `MvPolynomial (Fin k) A`.
* Over `ℤ_[p]`, both restricted-series carriers are `(p)`-adic, adically complete, and noetherian;
  their quotients modulo `(p) ^ m` (`0 < m`) are isomorphic to `(ℤ / p ^ m ℤ)[X₁, …, Xₖ]` (and
  `(ℤ / p ^ m ℤ)[X]` in one variable), with limit cone in `CommRingCat`.
* Because `PowerSeries ℤ_[p]` (`WithPiTopology`) and `ℤ_[p]⟨T⟩` carry complete Hausdorff linear
  topologies, restricted series over `ℤ_[p]` evaluate continuously at elements with unit constant
  term such as `1 + T`. By contrast, no continuous ring homomorphism from `ℤ_[p]⟨X⟩` to `ℚ_[p]`
  can send `X` to `p⁻¹`.
* The geometric series `∑ X ^ n` in `ℤ_[p]⟦X⟧` is restricted in neither carrier: its coefficients
  are all `1`, which does not tend to `0` in `ℤ_[p]`.
* At `k = 0`, `A⟨⟩` is the separated completion `UniformSpace.Completion A`: isomorphic to `A`
  when `A` is complete and Hausdorff, non-injectively receiving `A` when `A` carries the indiscrete
  `⊤`-adic topology, and non-surjectively receiving the `p`-adically topologised integers
  `⊥ ≤ ℤ_[p]`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.4.
* T. Wedhorn, *Adic Spaces*, §5.6.
* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §§5.1.1–5.1.3.
-/

public section

open CategoryTheory Limits Filter Topology IsLocalRing
open _root_.MvPowerSeries TauCeti TauCeti.Huber TauCeti.MvPowerSeries

section Discrete

-- Over a discrete commutative ring, completed restricted power series are polynomials.
noncomputable example (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    restrictedMvPowerSeriesCompletion k A ≃+* MvPolynomial (Fin k) A := by
  haveI : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
  haveI : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight) := IsRightUniformAddGroup.discreteUniformity
  exact (restrictedMvPowerSeriesCompletionEquiv k A).trans
    (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight).symm

-- Over a discrete ultrametric normed commutative ring, Gauss-normed restricted series are
-- polynomials.
noncomputable example (k : ℕ) (R : Type*) [NormedCommRing R] [IsUltrametricDist R]
    [DiscreteTopology R] :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ≃+* MvPolynomial (Fin k) R :=
  restrictedMvPowerSeriesGaussEquiv.symm.trans
    (weightedPolynomialEquivOfDiscrete (fun _ : Fin k ↦ ({1} : Set R))
      isWeightFamily_one_weight).symm

end Discrete

section Padic

variable (p : ℕ) [Fact p.Prime]

local instance : IsAdicRing ℤ_[p] :=
  ⟨maximalIdeal ℤ_[p],
    by rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _,
    TauCeti.Huber.PadicInt.isAdic_maximalIdeal, inferInstance⟩

-- Both carriers over `ℤ_[p]` are adic rings of finite ideal type and noetherian.
example (k : ℕ) :
    IsAdicRing (restrictedMvPowerSeriesCompletion k ℤ_[p]) ∧
      IsNoetherianRing (restrictedMvPowerSeriesCompletion k ℤ_[p]) ∧
      IsAdicRing (IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)) ∧
      IsNoetherianRing (IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1)) :=
  ⟨inferInstance,
    isNoetherianRing_restrictedMvPowerSeriesCompletion_of_isAdic k
      TauCeti.Huber.PadicInt.isAdic_maximalIdeal,
    inferInstance,
    isNoetherianRing_isRestricted_subring_of_isAdic k
      TauCeti.Huber.PadicInt.isAdic_maximalIdeal⟩

/-- Quotient of `ℤ_[p]` modulo `(p) ^ m` identified with `ZMod (p ^ m)`. -/
private noncomputable def padicIntQuotientPowEquivZMod (m : ℕ) :
    (ℤ_[p] ⧸ maximalIdeal ℤ_[p] ^ m) ≃+* ZMod (p ^ m) := by
  have hker : RingHom.ker (_root_.PadicInt.toZModPow m : ℤ_[p] →+* ZMod (p ^ m)) =
      maximalIdeal ℤ_[p] ^ m := by
    rw [_root_.PadicInt.ker_toZModPow, _root_.PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow]
  have hsurj : Function.Surjective (_root_.PadicInt.toZModPow m : ℤ_[p] →+* ZMod (p ^ m)) :=
    fun z ↦ ⟨z.val, by simp⟩
  exact (Ideal.quotEquivOfEq hker.symm).trans
    ((_root_.PadicInt.toZModPow m).quotientKerEquivOfSurjective hsurj)

-- Reduction of `ℤ_[p]⟨X₁, …, Xₖ⟩` modulo `(p) ^ m` (`0 < m`) is `(ℤ / p ^ m ℤ)[X₁, …, Xₖ]`.
noncomputable example (k : ℕ) {m : ℕ} (hm : 0 < m) :
    (restrictedMvPowerSeriesCompletion k ℤ_[p] ⧸
        ((maximalIdeal ℤ_[p]).map
          (algebraMap ℤ_[p] (restrictedMvPowerSeriesCompletion k ℤ_[p]))) ^ m) ≃+*
      MvPolynomial (Fin k) (ZMod (p ^ m)) :=
  (quotientRestrictedCompletionPowEquivMvPolynomialQuotient
    TauCeti.Huber.PadicInt.isAdic_maximalIdeal (IsNoetherian.noetherian _) hm).toRingEquiv.trans
    (MvPolynomial.mapEquiv _ (padicIntQuotientPowEquivZMod p m))

-- In one variable, reduction of Gauss-normed `ℤ_[p]⟨X⟩` modulo `(p) ^ m` (`0 < m`) is
-- `(ℤ / p ^ m ℤ)[X]`.
noncomputable example {m : ℕ} (hm : 0 < m) :
    (IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) ⧸
        ((maximalIdeal ℤ_[p]).map
          (algebraMap ℤ_[p] (IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1)))) ^ m) ≃+*
      Polynomial (ZMod (p ^ m)) :=
  ((quotientIsRestrictedSubringPowEquivMvPolynomialQuotient
    TauCeti.Huber.PadicInt.isAdic_maximalIdeal (IsNoetherian.noetherian _) hm).toRingEquiv.trans
    (MvPolynomial.mapEquiv _ (padicIntQuotientPowEquivZMod p m))).trans
    ((MvPolynomial.finSuccEquiv (ZMod (p ^ m)) 0).toRingEquiv.trans
      (Polynomial.mapEquiv (MvPolynomial.isEmptyAlgEquiv (ZMod (p ^ m)) (Fin 0)).toRingEquiv))

-- Both `ℤ_[p]⟨X₁, …, Xₖ⟩` carriers are limits of `(ℤ_[p] ⧸ (p) ^ (n + 1))[X₁, …, Xₖ]` in
-- `CommRingCat`.
noncomputable example (k : ℕ) :
    IsLimit (restrictedCompletionPolynomialCone k
        (TauCeti.Huber.PadicInt.isAdic_maximalIdeal (p := p))) ×
      IsLimit (isRestrictedSubringPolynomialCone k
        (TauCeti.Huber.PadicInt.isAdic_maximalIdeal (p := p))) :=
  (isLimitRestrictedCompletionPolynomialCone k TauCeti.Huber.PadicInt.isAdic_maximalIdeal
      (IsNoetherian.noetherian _),
    isLimitIsRestrictedSubringPolynomialCone k TauCeti.Huber.PadicInt.isAdic_maximalIdeal
      (IsNoetherian.noetherian _))

-- Linear-topology evaluation into `ℤ_[p]⟦T⟧` (`WithPiTopology`):
-- `restrictedMvPowerSeriesCompletion` evaluates continuously at `1 + T`, whose constant term `1`
-- is a unit rather than nilpotent.
open scoped MvPowerSeries.WithPiTopology PowerSeries.WithPiTopology in
example (k : ℕ) :
    ∃! ψ : restrictedMvPowerSeriesCompletion k ℤ_[p] →ₐ[ℤ_[p]] PowerSeries ℤ_[p],
      Continuous ψ ∧
        ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set ℤ_[p]))
            isWeightFamily_one_weight) : restrictedMvPowerSeriesCompletion k ℤ_[p]) =
          1 + (PowerSeries.X : PowerSeries ℤ_[p]) :=
  existsUnique_continuous_algHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology
    PowerSeries.WithPiTopology.continuous_C (fun _ ↦ 1 + (PowerSeries.X : PowerSeries ℤ_[p]))

-- Linear-topology evaluation on `IsRestricted.subring`: `ℤ_[p]⟨X₁, …, Xₖ⟩` evaluates continuously
-- in `ℤ_[p]⟨T⟩` at `1 + T` without requiring topological nilpotence.
example (k : ℕ) :
    ∃! ψ : IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin k ↦ 1) →ₐ[ℤ_[p]]
        IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1),
      Continuous ψ ∧ ∀ i, ψ ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ =
        1 + ⟨MvPowerSeries.X 0, isRestricted_X _ 0⟩ := by
  have hcont : Continuous
      (algebraMap ℤ_[p] (IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1))) :=
    (isometry_algebraMap_isRestrictedSubring (R := ℤ_[p]) (c := fun _ : Fin 1 ↦ 1)).continuous
  exact existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology hcont
    (fun _ ↦ 1 + ⟨MvPowerSeries.X 0, isRestricted_X _ 0⟩)

-- Boundary failure into `ℚ_[p]`: no continuous ring homomorphism from `ℤ_[p]⟨X⟩` to `ℚ_[p]` can
-- send `X` to `p⁻¹`, because `(p · X) ^ n → 0` in `ℤ_[p]⟨X⟩` while `(p · p⁻¹) ^ n = 1` in `ℚ_[p]`.
example :
    ¬ ∃ φ : IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) →+* ℚ_[p],
      Continuous φ ∧ φ ⟨MvPowerSeries.X 0, isRestricted_X _ 0⟩ = (p : ℚ_[p])⁻¹ := by
  rintro ⟨φ, hφ, hX⟩
  let x : IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) :=
    algebraMap ℤ_[p] _ (p : ℤ_[p]) * ⟨MvPowerSeries.X 0, isRestricted_X _ 0⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hx_lt : ‖x‖ < 1 := by
    refine lt_of_le_of_lt (MvPowerSeries.norm_le_iff.mpr fun ν ↦ ?_)
      (show ‖(p : ℤ_[p])‖ < 1 by
        rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt))
    have hc : coeff ν (x : MvPowerSeries (Fin 1) ℤ_[p]) =
        (p : ℤ_[p]) * coeff ν (MvPowerSeries.X 0) := by
      simp only [x, Subring.coe_mul, MvPowerSeries.coe_algebraMap_isRestrictedSubring,
        MvPowerSeries.coeff_C_mul]
    simp only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one, hc]
    calc ‖(p : ℤ_[p]) * coeff ν (MvPowerSeries.X 0)‖
        ≤ ‖(p : ℤ_[p])‖ * ‖coeff ν (MvPowerSeries.X 0)‖ := norm_mul_le _ _
      _ ≤ ‖(p : ℤ_[p])‖ * 1 := by
          gcongr; by_cases hν : ν = Finsupp.single 0 1 <;> simp [MvPowerSeries.coeff_X, hν]
      _ = ‖(p : ℤ_[p])‖ := mul_one _
  have h0 : Tendsto (fun n : ℕ ↦ φ (x ^ n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      (hφ.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx_lt)
  have h1 : (fun n : ℕ ↦ φ (x ^ n)) = fun _ ↦ (1 : ℚ_[p]) := by
    ext n
    have hxp : algebraMap ℤ_[p] (IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1)) p = p :=
      map_natCast _ p
    simp [x, hxp, map_pow, map_mul, hX, hp0]
  exact one_ne_zero (tendsto_nhds_unique (h1 ▸ tendsto_const_nhds) h0)

-- The geometric series `∑ X ^ n` in `ℤ_[p]⟦X⟧` is restricted in neither carrier.
example :
    ¬ (PowerSeries.mk (1 : ℕ → ℤ_[p])).IsRestricted 1 ∧
      ((fun _ : Fin 1 →₀ ℕ ↦ (1 : ℤ_[p])) : MvPowerSeries (Fin 1) ℤ_[p]) ∉
        weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set ℤ_[p]))
          isWeightFamily_one_weight := by
  refine ⟨PowerSeries.not_isRestricted_mk_one, fun h ↦ ?_⟩
  have h' : Tendsto (fun _ : Fin 1 →₀ ℕ ↦ (1 : ℤ_[p])) cofinite (𝓝 0) :=
    isWeightedRestricted_one_weight_iff.mp
      (mem_weightedRestrictedSubring (f := (fun _ : Fin 1 →₀ ℕ ↦ (1 : ℤ_[p]))).mp h)
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h')

end Padic

section ZeroVariables

-- At `k = 0`, `A⟨⟩` is the separated completion `UniformSpace.Completion A`, and agrees with `A`
-- when `A` is complete and Hausdorff for its additive uniformity.
noncomputable example (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [T0Space A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    ∀ [CompleteSpace A], restrictedMvPowerSeriesCompletion 0 A ≃+* A := by
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  intro _
  exact restrictedMvPowerSeriesCompletionFinZeroEquiv.trans
    (UniformSpace.Completion.completeRingEquivSelf A)

-- When `R` is nontrivial and carries the indiscrete `⊤`-adic topology, `algebraMap R R⟨⟩` fails
-- injectivity: `R⟨⟩` is `⊤`-adically complete and hence the zero ring.
example (R : Type*) [CommRing R] [Nontrivial R] :
    letI : TopologicalSpace R := (⊤ : Ideal R).adicTopology
    haveI : NonarchimedeanRing R := (⊤ : Ideal R).nonarchimedean
    ¬ Function.Injective (algebraMap R (restrictedMvPowerSeriesCompletion 0 R)) := by
  let _ : TopologicalSpace R := (⊤ : Ideal R).adicTopology
  have _ : NonarchimedeanRing R := (⊤ : Ideal R).nonarchimedean
  have htop : IsAdic (⊤ : Ideal R) := rfl
  have hc := isAdicComplete_map_algebraMap_restrictedMvPowerSeriesCompletion 0 htop
    ⟨{1}, by simp⟩
  rw [Ideal.map_top] at hc
  have : Subsingleton (restrictedMvPowerSeriesCompletion 0 R) := hc.toIsHausdorff.subsingleton
  intro hinj
  exact zero_ne_one (hinj (Subsingleton.elim _ _))

-- When `A` is Hausdorff (`⊥ ≤ ℤ_[p]`, integers with the `p`-adic subspace topology) but not
-- complete, `algebraMap A A⟨⟩` is injective yet not surjective: `1 + p` becomes a unit in `A⟨⟩`.
example (p : ℕ) [Fact p.Prime] :
    let R₀ := (⊥ : Subring ℤ_[p])
    Function.Injective (algebraMap R₀ (restrictedMvPowerSeriesCompletion 0 R₀)) ∧
      ¬ Function.Surjective (algebraMap R₀ (restrictedMvPowerSeriesCompletion 0 R₀)) := by
  intro R₀
  let C := restrictedMvPowerSeriesCompletion 0 R₀
  have hinj : Function.Injective (algebraMap R₀ C) := by
    have hsub : Continuous ⇑R₀.subtype := continuous_subtype_val
    intro a b hab
    exact Subtype.ext <|
      (restrictedCompletionEvalLinear_algebraMap hsub Fin.elim0 a).symm.trans <|
        (congrArg (restrictedCompletionEvalLinear hsub Fin.elim0) hab).trans
          (restrictedCompletionEvalLinear_algebraMap hsub Fin.elim0 b)
  refine ⟨hinj, fun hsurj ↦ ?_⟩
  have hp_lt : ‖(p : R₀)‖ < 1 := by
    change ‖(p : ℤ_[p])‖ < 1
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt)
  have hp_nil : IsTopologicallyNilpotent (p : C) := by
    rw [IsTopologicallyNilpotent]
    have hcont : Continuous (algebraMap R₀ C) :=
      (UniformSpace.Completion.continuous_coe _).comp
        (continuous_weightedC isWeightFamily_one_weight)
    simpa only [Function.comp_def, map_pow, map_natCast, map_zero] using
      (hcont.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp_lt)
  obtain ⟨u, hu⟩ := hp_nil.isUnit_one_add
  obtain ⟨b, hb⟩ := hsurj ↑u⁻¹
  obtain ⟨m, hm⟩ := Subring.mem_bot.mp b.2
  have hb_eq : b = (m : R₀) := Subtype.ext hm.symm
  subst hb_eq
  have hmul : algebraMap R₀ C (((1 + p : ℤ) * m : ℤ)) = algebraMap R₀ C 1 := by
    calc algebraMap R₀ C (((1 + p : ℤ) * m : ℤ))
        = (1 + (p : C)) * algebraMap R₀ C (m : R₀) := by simp
      _ = 1 := by rw [hb, ← hu, Units.mul_inv]
      _ = algebraMap R₀ C 1 := (map_one _).symm
  have hm1 : (1 + (p : ℤ)) * m = 1 := by
    have hsub := congrArg (fun x : R₀ ↦ (x : ℤ_[p])) (hinj hmul)
    exact_mod_cast hsub
  have hunit : IsUnit (1 + (p : ℤ)) := IsUnit.of_mul_eq_one m hm1
  rcases Int.isUnit_iff.mp hunit with h | h <;>
    exact absurd h (by have := (Fact.out : p.Prime).two_le; omega)

end ZeroVariables

end
