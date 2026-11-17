/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Padic.Restricted
import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Checks for adic restricted power series and Gauss comparisons

Concrete checks for restricted power series over discrete rings, `ℤ_[p]`, and zero variables:
(1) discrete restricted series equal polynomials on both carriers; (2) reducing `ℤ_[p]⟨X₁, …, Xₙ⟩`
modulo `p ^ m` gives `(ZMod (p ^ m))[X₁, …, Xₙ]` compatibly across the Gauss comparison;
(3) `∑ X ^ n` lies in `ℤ_[p]⟦X⟧` but in neither restricted-series subring; (4) in zero variables,
`restrictedMvPowerSeriesCompletion 0 A ≃+* UniformSpace.Completion A`, isomorphic to `A` under
completeness and separatedness (with both hypotheses sharp on indiscrete `ℤ` and `(3)`-adic `ℤ`);
(5) linearly topologised `ℤ_[p]`-algebras admit evaluation at arbitrary tuples, while `p⁻¹ ∈ ℚ_[p]`
is not power-bounded.
-/

public section

namespace TauCeti.Examples.HuberRestricted

open Filter Topology UniformSpace TauCeti.Huber TauCeti.Huber.PadicInt TauCeti.MvPowerSeries

/-! ### 1. Discrete coefficient rings: restricted series are polynomials -/

noncomputable example {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [DiscreteTopology A] (k : ℕ) :
    MvPolynomial (Fin k) A ≃+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight

example {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [DiscreteTopology R]
    {c : σ → ℝ} (hc : ∀ i, 1 ≤ c i) :
    Function.Bijective (polynomialToRestricted (R := R) c) :=
  polynomialToRestricted_bijective_of_discreteTopology hc

/-! ### 2. Reduction of `ℤ_[p]⟨X₁, …, Xₙ⟩` modulo `p ^ m` -/

section PadicChecks

variable (p : ℕ) [Fact p.Prime]

example (n m : ℕ)
    (q : restrictedMvPowerSeriesCompletion n ℤ_[p] ⧸
      Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p]) ^ m}) :
    quotientSpanPowIsRestrictedEquivMvPolynomialZMod n m
        (Ideal.quotientEquiv _ _
          (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := ℤ_[p]))
          (by rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]) q) =
      quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod n m q :=
  quotientSpanPowIsRestrictedEquivMvPolynomialZMod_quotientEquiv n m q

/-- Reducing `1 + p X₀ + p² X₀² ∈ ℤ_[p]⟨X₀⟩` modulo `p ^ 2` kills `p² X₀²` and leaves `1 + p X₀`
in `(ZMod (p ^ 2))[X₀]`. -/
theorem coeff_reduction_quadratic_mod_p_sq :
    let q : MvPolynomial (Fin 1) ℤ_[p] :=
      1 + MvPolynomial.C (p : ℤ_[p]) * MvPolynomial.X 0 +
        MvPolynomial.C ((p : ℤ_[p]) ^ 2) * MvPolynomial.X 0 ^ 2
    let f : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) :=
      polynomialToRestricted (fun _ : Fin 1 ↦ 1) q
    let red := quotientSpanPowIsRestrictedEquivMvPolynomialZMod (p := p) 1 2
      (Ideal.Quotient.mk _ f)
    red.coeff 0 = 1 ∧ red.coeff (Finsupp.single 0 1) = p ∧
      red.coeff (Finsupp.single 0 2) = 0 := by
  intro q f red
  have hred (ν : Fin 1 →₀ ℕ) : red.coeff ν =
      _root_.PadicInt.toZModPow 2
        ((1 : MvPolynomial (Fin 1) ℤ_[p]).coeff ν +
          (p : ℤ_[p]) * (MvPolynomial.X (R := ℤ_[p]) 0).coeff ν +
          ((p : ℤ_[p]) ^ 2) * (MvPolynomial.X (R := ℤ_[p]) 0 ^ 2).coeff ν) := by
    dsimp only [red, f]
    rw [coeff_quotientSpanPowIsRestrictedEquivMvPolynomialZMod_mk, coe_polynomialToRestricted,
      MvPolynomial.coeff_coe]
    simp only [q, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul]
  refine ⟨by simp [hred, MvPolynomial.coeff_X, MvPolynomial.coeff_X_pow],
    by simp [hred, MvPolynomial.coeff_one, MvPolynomial.coeff_X, MvPolynomial.coeff_X_pow,
      eq_comm (a := (0 : Fin 1 →₀ ℕ)), Finsupp.single_eq_zero], ?_⟩
  simpa [hred, MvPolynomial.coeff_one, MvPolynomial.coeff_X, MvPolynomial.coeff_X_pow,
    eq_comm (a := (0 : Fin 1 →₀ ℕ)), Finsupp.single_eq_zero] using
    (Nat.cast_pow (α := ZMod (p ^ 2)) p 2).symm.trans (ZMod.natCast_self (p ^ 2))

/-! ### 3. `∑ X ^ n` lies in `ℤ_[p]⟦X⟧` but not in `ℤ_[p]⟨X⟩` -/

/-- The geometric series `∑_{n ≥ 0} X ^ n` over `ℤ_[p]` is neither Gauss- nor Huber-restricted. -/
theorem geometricSeries_not_mem_restricted :
    let geom : MvPowerSeries (Fin 1) ℤ_[p] := fun _ ↦ 1
    geom ∉ MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) ∧
      geom ∉ weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set ℤ_[p]))
        isWeightFamily_one_weight := by
  intro geom
  have hnot : geom ∉ MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) := by
    intro hmem
    have hfin : {ν : Fin 1 →₀ ℕ | (1 : ℝ) ≤ ‖MvPowerSeries.coeff ν geom‖}.Finite := by
      simpa [eventually_cofinite, not_lt] using hmem.eventually (gt_mem_nhds zero_lt_one)
    refine Set.infinite_range_of_injective (Finsupp.single_injective (0 : Fin 1)) (hfin.subset ?_)
    rintro _ ⟨n, rfl⟩; rw [Set.mem_ofPred_eq, MvPowerSeries.coeff_apply]; simp [geom]
  exact ⟨hnot, by rwa [weightedRestrictedSubring_eq_isRestricted_subring]⟩

/-! ### 5. Linearly topologised vs normed universal property over `ℤ_[p]` -/

example (b : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1)) :
    (∃! ψ : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) →ₐ[ℤ_[p]]
        MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1),
      Continuous ψ ∧ ψ ⟨MvPowerSeries.X 0, MvPowerSeries.isRestricted_X _ 0⟩ = b) ∧
      ¬ IsPowerBounded ((p : ℚ_[p])⁻¹) :=
  ⟨by simpa [Fin.forall_fin_one] using
      existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology
        (R := ℤ_[p]) (T := MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1))
        _root_.MvPowerSeries.isometry_algebraMap_isRestrictedSubring.continuous (fun _ : Fin 1 ↦ b),
    by rw [isPowerBounded_iff_norm_le_one, norm_inv, Padic.norm_p, inv_inv, not_le]
       exact mod_cast (Fact.out : p.Prime).one_lt⟩

end PadicChecks

/-! ### 4. Zero variables: separated completion and sharpness of both hypotheses -/

section ZeroVariables

noncomputable example (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    restrictedMvPowerSeriesCompletion 0 A ≃+* Completion A :=
  restrictedMvPowerSeriesCompletionFinZeroEquiv

noncomputable example (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [NonarchimedeanRing A] [CompleteSpace A] [T0Space A] :
    restrictedMvPowerSeriesCompletion 0 A ≃+* A :=
  (restrictedMvPowerSeriesCompletionEquiv 0 A).trans
    (weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A)))

private def IndiscreteInt : Type := ℤ

private instance : CommRing IndiscreteInt := inferInstanceAs (CommRing ℤ)
private instance : Nontrivial IndiscreteInt := inferInstanceAs (Nontrivial ℤ)
private instance : WithIdeal IndiscreteInt := ⟨⊤⟩

/-- Sharpness when separatedness fails: `(⊤)`-adic `ℤ` is complete, fails `T0Space`, and has
trivial zero-variable restricted-series completion. -/
example : CompleteSpace IndiscreteInt ∧ ¬ T0Space IndiscreteInt ∧
    IsEmpty (restrictedMvPowerSeriesCompletion 0 IndiscreteInt ≃+* IndiscreteInt) := by
  have h0 : 𝓝 (0 : IndiscreteInt) = ⊤ :=
    ((⊤ : Ideal IndiscreteInt).hasBasis_nhds_zero_adic).eq_top_iff.mpr fun _ _ ↦ by simp
  have hnhds (x : IndiscreteInt) : 𝓝 x = ⊤ := by
    rw [← map_add_left_nhds_zero x, h0, Filter.ext_iff]
    exact fun s ↦ ⟨fun h y ↦ by simpa using h (y - x), fun h y ↦ h _⟩
  have hnil_comp :
      IsTopologicallyNilpotent (1 : restrictedMvPowerSeriesCompletion 0 IndiscreteInt) := by
    rw [← map_one (algebraMap IndiscreteInt (restrictedMvPowerSeriesCompletion 0 IndiscreteInt))]
    exact (WithIdeal.isTopologicallyNilpotent_of_mem Submodule.mem_top).map
      (continuous_algebraMap_restrictedMvPowerSeriesCompletion 0 IndiscreteInt)
  have hu0 : IsUnit (0 : restrictedMvPowerSeriesCompletion 0 IndiscreteInt) := by
    simpa using hnil_comp.isUnit_one_sub
  have hinsep : Inseparable (0 : IndiscreteInt) 1 := by rw [Inseparable, hnhds 0, hnhds 1]
  refine ⟨⟨fun {_} _ ↦ ⟨0, h0 ▸ le_top⟩⟩, fun ht0 ↦ zero_ne_one hinsep.eq,
    ⟨fun e ↦ not_isUnit_zero (map_zero e ▸ hu0.map e)⟩⟩

private def ThreeAdicInt : Type := ℤ

private instance : CommRing ThreeAdicInt := inferInstanceAs (CommRing ℤ)
private instance : WithIdeal ThreeAdicInt := ⟨Ideal.span {3}⟩

private def threeAdicIntEquiv : ThreeAdicInt ≃+* ℤ := RingEquiv.refl ℤ

private theorem t2Space_threeAdicInt : T2Space ThreeAdicInt := by
  have hadic : IsAdic (Ideal.span {(3 : ThreeAdicInt)}) := rfl
  refine hadic.isHausdorff_iff.mp ⟨fun x hx ↦ ?_⟩
  by_contra hx0
  let z : ℤ := threeAdicIntEquiv x
  have hz0 : z ≠ 0 := by rwa [Ne, map_eq_zero_iff threeAdicIntEquiv threeAdicIntEquiv.injective]
  have hmem := SModEq.sub_mem.mp (hx z.natAbs)
  rw [sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hmem
  have hdvd : (3 : ℤ) ^ z.natAbs ∣ z := by
    simpa only [z, map_pow, map_ofNat] using map_dvd threeAdicIntEquiv hmem
  exact (Nat.lt_pow_self (by decide : 1 < 3)).not_ge
    (by simpa using Int.natAbs_le_of_dvd_ne_zero hdvd hz0)

/-- Sharpness when completeness fails: `(3)`-adic `ℤ` is Hausdorff, fails `CompleteSpace`, and is
not ring-isomorphic to its zero-variable completion (where `4 = 1 + 3` is a unit). -/
example : T2Space ThreeAdicInt ∧ ¬ CompleteSpace ThreeAdicInt ∧
    IsEmpty (restrictedMvPowerSeriesCompletion 0 ThreeAdicInt ≃+* ThreeAdicInt) := by
  have ht2 : T2Space ThreeAdicInt := t2Space_threeAdicInt
  have hemp : IsEmpty (restrictedMvPowerSeriesCompletion 0 ThreeAdicInt ≃+* ThreeAdicInt) :=
    ⟨fun e ↦ by
      have hu4 : IsUnit (4 : restrictedMvPowerSeriesCompletion 0 ThreeAdicInt) := by
        have h4 : (4 : restrictedMvPowerSeriesCompletion 0 ThreeAdicInt) =
            1 + algebraMap ThreeAdicInt _ 3 := by rw [map_ofNat]; norm_num
        rw [h4]
        exact ((WithIdeal.isTopologicallyNilpotent_of_mem
          (Ideal.mem_span_singleton_self (3 : ThreeAdicInt))).map
            (continuous_algebraMap_restrictedMvPowerSeriesCompletion 0 ThreeAdicInt)).isUnit_one_add
      have huZ : IsUnit (4 : ℤ) := by
        simpa only [map_ofNat] using hu4.map (e.trans threeAdicIntEquiv)
      rcases Int.isUnit_iff.mp huZ with h | h <;> omega⟩
  have hnot_comp : ¬ CompleteSpace ThreeAdicInt := fun hcomp ↦
    hemp.false ((restrictedMvPowerSeriesCompletionEquiv 0 ThreeAdicInt).trans
      (weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set ThreeAdicInt))))
  exact ⟨ht2, hnot_comp, hemp⟩

end ZeroVariables

end TauCeti.Examples.HuberRestricted
