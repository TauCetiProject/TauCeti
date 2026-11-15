/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Padic.Field
public import TauCeti.RingTheory.Huber.Padic.Restricted
import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Checks for adic restricted power series and Gauss comparisons

Concrete checks for restricted power series over discrete rings, `ℤ_[p]`, and zero-variable
completions:

1. Over a discrete ring `A`, restricted power series coincide with polynomials on both the Huber
   and Gauss-normed carriers.
2. Over `ℤ_[p]` with its `(p)`-adic topology, reducing `ℤ_[p]⟨X₁, …, Xₙ⟩` modulo `p ^ m` gives
   `(ZMod (p ^ m))[X₁, …, Xₙ]` on both carriers, compatibly with the Gauss comparison.
3. The geometric series `∑ X ^ n` lies in the formal power-series ring `ℤ_[p]⟦X⟧` but in neither
   the Gauss-normed nor the Huber restricted-series subring over `ℤ_[p]`.
4. In zero variables, `restrictedMvPowerSeriesCompletion 0 A` is `UniformSpace.Completion A`, and
   is isomorphic to `A` under completeness and separatedness, while both hypotheses are sharp:
   neither an indiscrete complete ring nor `(3)`-adic `ℤ` (Hausdorff, non-complete) is isomorphic
   as a ring to its zero-variable restricted-series completion.
5. Into a complete Hausdorff linearly topologised `ℤ_[p]`-algebra, arbitrary variable images
   extend uniquely, whereas in `ℚ_[p]` an element of norm greater than `1` is not power-bounded.
-/

public section

namespace TauCeti.Examples.HuberRestricted

open Filter Topology UniformSpace TauCeti.Huber TauCeti.Huber.PadicInt TauCeti.MvPowerSeries

/-! ### 1. Discrete coefficient rings: restricted series are polynomials -/

/-- Over a discrete nonarchimedean ring `A`, the Huber restricted-series ring is isomorphic to the
polynomial ring `MvPolynomial (Fin k) A`. -/
noncomputable example {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [DiscreteTopology A] (k : ℕ) :
    MvPolynomial (Fin k) A ≃+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight

/-- Over a discrete ultrametric normed ring `R`, the polynomial inclusion into Gauss-normed
unit-radius restricted series is bijective. -/
theorem polynomialToRestricted_bijective_of_discreteTopology {R : Type*} [NormedCommRing R]
    [IsUltrametricDist R] [DiscreteTopology R] (k : ℕ) :
    Function.Bijective
      (polynomialToRestricted (R := R) (fun _ : Fin k ↦ (1 : ℝ))) := by
  have hcomp :
      ⇑(polynomialToRestricted (R := R) (fun _ : Fin k ↦ (1 : ℝ))) =
        ⇑(restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)) ∘
          ⇑(weightedPolynomialEquivOfDiscrete
            (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) := by
    ext p : 1
    dsimp only [Function.comp_apply]
    rw [weightedPolynomialEquivOfDiscrete_apply,
      restrictedMvPowerSeriesGaussEquiv_weightedPolynomialHom]
  rw [hcomp]
  exact (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).bijective.comp
    (weightedPolynomialEquivOfDiscrete _ isWeightFamily_one_weight).bijective

/-! ### 2. Reduction of `ℤ_[p]⟨X₁, …, Xₙ⟩` modulo `p ^ m` -/

section PadicChecks

variable (p : ℕ) [Fact p.Prime]

/-- Reduction of `ℤ_[p]⟨X₁, …, Xₙ⟩` modulo `p ^ m` is `(ZMod (p ^ m))[X₁, …, Xₙ]` on both the
Gauss-normed and completed Huber carriers, and the two identifications commute with the Gauss
comparison. -/
example (n m : ℕ)
    (q : restrictedMvPowerSeriesCompletion n ℤ_[p] ⧸
      Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p]) ^ m}) :
    quotientSpanPowIsRestrictedEquivMvPolynomialZMod n m
        (Ideal.quotientEquiv _ _
          (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := ℤ_[p]))
          (by rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]) q) =
      quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod n m q :=
  quotientSpanPowIsRestrictedEquivMvPolynomialZMod_quotientEquiv n m q

/-- Reducing `1 + p X₀ + p² X₀² ∈ ℤ_[p]⟨X₀⟩` modulo `p ^ 2` kills the `p² X₀²` term and leaves
constant coefficient `1` and linear coefficient `p` in `ZMod (p ^ 2)`. -/
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
  have hq : q = 1 + MvPolynomial.monomial (Finsupp.single 0 1) (p : ℤ_[p]) +
      MvPolynomial.monomial (Finsupp.single 0 2) ((p : ℤ_[p]) ^ 2) := by
    dsimp only [q]
    rw [← MvPolynomial.C_mul_X_pow_eq_monomial, ← MvPolynomial.C_mul_X_pow_eq_monomial, pow_one]
  have hred (ν : Fin 1 →₀ ℕ) : red.coeff ν = _root_.PadicInt.toZModPow 2 (q.coeff ν) := by
    dsimp only [red, f]
    rw [coeff_quotientSpanPowIsRestrictedEquivMvPolynomialZMod_mk, coe_polynomialToRestricted,
      MvPolynomial.coeff_coe]
  have h01 : (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    simpa using DFunLike.congr_fun h 0
  have h02 : (0 : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 2 := by
    intro h
    simpa using DFunLike.congr_fun h 0
  have h12 : (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 2 := by
    intro h
    simpa using DFunLike.congr_fun h 0
  refine ⟨?_, ?_, ?_⟩
  · rw [hred, hq]
    simp [MvPolynomial.coeff_monomial, h01.symm, h02.symm]
  · rw [hred, hq]
    simp [MvPolynomial.coeff_one, MvPolynomial.coeff_monomial, h01, h12.symm]
  · rw [hred, hq]
    have hcoeff : q.coeff (Finsupp.single 0 2) = (p : ℤ_[p]) ^ 2 := by
      rw [hq]
      simp [MvPolynomial.coeff_one, MvPolynomial.coeff_monomial, h02, h12]
    rw [← hq, hcoeff, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]

/-! ### 3. `∑ X ^ n` lies in `ℤ_[p]⟦X⟧` but not in `ℤ_[p]⟨X⟩` -/

/-- The geometric series `∑_{n ≥ 0} X ^ n` in one variable over `ℤ_[p]` is a formal power series
that is neither Gauss-restricted at radius `1` nor Huber-restricted over `ℤ_[p]`. -/
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
    have hinf : ¬ (Set.range fun n : ℕ ↦ Finsupp.single (0 : Fin 1) n).Finite :=
      Set.infinite_range_of_injective (Finsupp.single_injective 0)
    refine hinf (hfin.subset ?_)
    rintro _ ⟨n, rfl⟩
    rw [Set.mem_ofPred_eq, MvPowerSeries.coeff_apply]
    simp [geom]
  refine ⟨hnot, ?_⟩
  rwa [weightedRestrictedSubring_eq_isRestricted_subring]

/-! ### 5. Linearly topologised vs normed universal property over `ℤ_[p]` -/

/-- Into the linearly topologised `ℤ_[p]`-algebra `ℤ_[p]⟨Y⟩`, every choice `b` of image for `X`
extends uniquely to a continuous `ℤ_[p]`-algebra homomorphism, agreeing on both carriers; whereas
in `ℚ_[p]`, `p⁻¹` has norm `p > 1` and is not power-bounded. -/
example (b : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1)) :
    (∃! ψ : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1) →ₐ[ℤ_[p]]
        MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1),
      Continuous ψ ∧ ψ ⟨MvPowerSeries.X 0, MvPowerSeries.isRestricted_X _ 0⟩ = b) ∧
      ¬ IsPowerBounded ((p : ℚ_[p])⁻¹) := by
  refine ⟨?_, ?_⟩
  · simpa [Fin.forall_fin_one] using
      existsUnique_continuous_algHom_isRestricted_subring_of_isLinearTopology
        (R := ℤ_[p]) (S := MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin 1 ↦ 1))
        _root_.MvPowerSeries.isometry_algebraMap_isRestrictedSubring.continuous (fun _ : Fin 1 ↦ b)
  · rw [isPowerBounded_iff_norm_le_one, norm_inv, Padic.norm_p, inv_inv, not_le]
    exact mod_cast (Fact.out : p.Prime).one_lt

end PadicChecks

/-! ### 4. Zero variables: separated completion and sharpness of both hypotheses -/

section ZeroVariables

/-- In zero variables, `restrictedMvPowerSeriesCompletion 0 A` is the separated completion
`UniformSpace.Completion A` for the additive group uniformity of `A`. -/
noncomputable example (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    restrictedMvPowerSeriesCompletion 0 A ≃+* Completion A :=
  restrictedMvPowerSeriesCompletionFinZeroEquiv

/-- When `A` is complete and separated (`T0Space`), the zero-variable completion is `A` itself. -/
noncomputable example (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [NonarchimedeanRing A] [CompleteSpace A] [T0Space A] :
    restrictedMvPowerSeriesCompletion 0 A ≃+* A :=
  (restrictedMvPowerSeriesCompletionEquiv 0 A).trans
    (weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set A)))

/-- `ℤ` equipped with the `(⊤)`-adic (indiscrete) topology: complete, but not `T0Space`. -/
private def IndiscreteInt : Type := ℤ

private instance : CommRing IndiscreteInt := inferInstanceAs (CommRing ℤ)
private instance : Nontrivial IndiscreteInt := inferInstanceAs (Nontrivial ℤ)
private instance : WithIdeal IndiscreteInt := ⟨⊤⟩

/-- Sharpness when separatedness fails: `IndiscreteInt` is complete and nonarchimedean, fails
`T0Space`, and has trivial zero-variable restricted-series completion, so no ring equivalence
`restrictedMvPowerSeriesCompletion 0 IndiscreteInt ≃+* IndiscreteInt` exists. -/
example : CompleteSpace IndiscreteInt ∧ ¬ T0Space IndiscreteInt ∧
    IsEmpty (restrictedMvPowerSeriesCompletion 0 IndiscreteInt ≃+* IndiscreteInt) := by
  have h0 : 𝓝 (0 : IndiscreteInt) = ⊤ := by
    rw [((⊤ : Ideal IndiscreteInt).hasBasis_nhds_zero_adic).eq_top_iff]
    exact fun _ _ ↦ by simp
  have hnhds (x : IndiscreteInt) : 𝓝 x = ⊤ := by
    rw [← map_add_left_nhds_zero x, h0, Filter.ext_iff]
    intro s
    simp only [Filter.mem_map, Filter.mem_top, Set.eq_univ_iff_forall, Set.mem_preimage]
    exact ⟨fun h y ↦ by simpa using h (y - x), fun h y ↦ h _⟩
  have hcomp : CompleteSpace IndiscreteInt :=
    ⟨fun {f} _ ↦ ⟨0, by rw [h0]; exact le_top⟩⟩
  have hnot_t0 : ¬ T0Space IndiscreteInt := by
    intro ht0
    have hinsep : Inseparable (0 : IndiscreteInt) 1 := by
      rw [Inseparable, hnhds 0, hnhds 1]
    exact zero_ne_one hinsep.eq
  have hnil1 : IsTopologicallyNilpotent (1 : IndiscreteInt) :=
    WithIdeal.isTopologicallyNilpotent_of_mem Submodule.mem_top
  have hu0 : IsUnit (0 : restrictedMvPowerSeriesCompletion 0 IndiscreteInt) := by
    have hnil_comp : IsTopologicallyNilpotent
        (1 : restrictedMvPowerSeriesCompletion 0 IndiscreteInt) := by
      rw [← map_one (algebraMap IndiscreteInt (restrictedMvPowerSeriesCompletion 0 IndiscreteInt))]
      exact hnil1.map (continuous_algebraMap_restrictedMvPowerSeriesCompletion 0 IndiscreteInt)
    have hu := hnil_comp.isUnit_one_sub
    rwa [sub_self] at hu
  refine ⟨hcomp, hnot_t0, ⟨fun e ↦ ?_⟩⟩
  have hu0' : IsUnit (0 : IndiscreteInt) := by
    rw [← map_zero e]
    exact hu0.map e
  exact not_isUnit_zero hu0'

/-- `ℤ` equipped with the `(3)`-adic topology: Hausdorff (`T2Space`), but not complete. -/
private def ThreeAdicInt : Type := ℤ

private instance : CommRing ThreeAdicInt := inferInstanceAs (CommRing ℤ)
private instance : WithIdeal ThreeAdicInt := ⟨Ideal.span {3}⟩

private theorem t2Space_threeAdicInt : T2Space ThreeAdicInt := by
  have hadic : IsAdic (Ideal.span {(3 : ThreeAdicInt)}) := rfl
  have hhaus : IsHausdorff (Ideal.span {(3 : ThreeAdicInt)}) ThreeAdicInt := by
    refine ⟨fun x hx ↦ ?_⟩
    by_contra hx0
    let z : ℤ := x
    have hz0 : z ≠ 0 := hx0
    have hmem : x - 0 ∈ Ideal.span {(3 : ThreeAdicInt)} ^ z.natAbs • (⊤ : Ideal ThreeAdicInt) :=
      SModEq.sub_mem.mp (hx z.natAbs)
    rw [sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hmem
    have hdvd : (3 : ℤ) ^ z.natAbs ∣ z := hmem
    have hle : (3 : ℕ) ^ z.natAbs ≤ z.natAbs := by
      simpa using Int.natAbs_le_of_dvd_ne_zero hdvd hz0
    exact (Nat.lt_pow_self (by decide : 1 < 3)).not_ge hle
  exact hadic.isHausdorff_iff.mp hhaus

/-- Sharpness when completeness fails: `ThreeAdicInt` is Hausdorff and nonarchimedean, fails
`CompleteSpace`, and is not even abstractly ring-isomorphic to its zero-variable restricted-series
completion (in which `4 = 1 + 3` becomes a unit). -/
example : T2Space ThreeAdicInt ∧ ¬ CompleteSpace ThreeAdicInt ∧
    IsEmpty (restrictedMvPowerSeriesCompletion 0 ThreeAdicInt ≃+* ThreeAdicInt) := by
  have ht2 : T2Space ThreeAdicInt := t2Space_threeAdicInt
  have hemp : IsEmpty (restrictedMvPowerSeriesCompletion 0 ThreeAdicInt ≃+* ThreeAdicInt) := by
    refine ⟨fun e ↦ ?_⟩
    have hnil3 : IsTopologicallyNilpotent (3 : ThreeAdicInt) :=
      WithIdeal.isTopologicallyNilpotent_of_mem (Ideal.mem_span_singleton_self _)
    have hu4 : IsUnit (4 : restrictedMvPowerSeriesCompletion 0 ThreeAdicInt) := by
      have h4 : (4 : restrictedMvPowerSeriesCompletion 0 ThreeAdicInt) =
          1 + algebraMap ThreeAdicInt _ 3 := by
        rw [map_ofNat]
        norm_num
      rw [h4]
      exact (hnil3.map
        (continuous_algebraMap_restrictedMvPowerSeriesCompletion 0 ThreeAdicInt)).isUnit_one_add
    have he4 : e 4 = (4 : ThreeAdicInt) := map_ofNat e 4
    have huZ : IsUnit (4 : ℤ) := by
      change IsUnit (4 : ThreeAdicInt)
      rw [← he4]
      exact hu4.map e
    rcases Int.isUnit_iff.mp huZ with h | h <;> omega
  have hnot_comp : ¬ CompleteSpace ThreeAdicInt := fun hcomp ↦
    hemp.false ((restrictedMvPowerSeriesCompletionEquiv 0 ThreeAdicInt).trans
      (weightedRestrictedSubringFinZeroEquiv (fun _ : Fin 0 ↦ ({1} : Set ThreeAdicInt))))
  exact ⟨ht2, hnot_comp, hemp⟩

end ZeroVariables

end TauCeti.Examples.HuberRestricted
