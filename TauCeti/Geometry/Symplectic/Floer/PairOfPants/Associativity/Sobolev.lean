/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Associativity
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.Sobolev

/-!
# The linearized Floer operator along the associativity family on `W^{1,2}`

The associativity of the pair-of-pants product compares the two compositions `(x₁ x₂) x₃` and
`x₁ (x₂ x₃)` through the one-parameter family of Floer data
`K_τ = TauCeti.Floer.associativityPerturbation H Hout G G' L τ`, `τ ∈ ℝ`, on spheres with three
moving input ends: the datum `Σ_τ` of the moving input ends along the associativity path, with
centers `c_τ = TauCeti.Floer.associativityCenter` and scales `TauCeti.Floer.associativityScale` of
plumbing factor `e^{-2πL} / 4`, plus the neck data of the two compositions switched on for `τ < 0`
and for `τ > 1`.

This file realizes the linearized Floer operator `D_u` of `K_τ` as the bounded operator
`D_u : W^{1,2}_0 → L²` of `TauCeti.SymplecticForm.floerConformalSobolevOperator` on the sphere
minus the centers `c_τ`, for the weight `TauCeti.Floer.movingEndsWeight c_τ`, and proves the first
half of its Fredholm property at every member `τ` of the family and every neck length `L > 4`:
along a map `u` that solves the Floer equation of `K_τ` on the ends and converges there to
nondegenerate orbits, `D_u` has finite-dimensional kernel
(`finiteDimensional_ker_floerConformalSobolevOperator_associativityPerturbation`) and closed range
(`isClosed_range_floerConformalSobolevOperator_associativityPerturbation`), both in the namespace
`TauCeti.SymplecticForm`.

On the part `s > 0` of every input end and the part `s ≥ 1` of the output end the neck data vanish
and `K_τ` is `Σ_τ` (`TauCeti.Floer.associativityPerturbation_realChart_eq`,
`TauCeti.Floer.associativityPerturbation_positiveEndChart_inf_eq`), and `K_τ` is smooth off the
centers (`TauCeti.Floer.contDiffAt_uncurry_associativityPerturbation`). So both results are the
case of the realization on spheres with moving input ends,
`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_of_movingEnds` and
`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_of_movingEnds`, for Floer
data equal to `Σ_τ` on the ends.

The target is a symplectic vector space. The finiteness of the cokernel and the Fredholm index are
not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and the associativity of
  the product through families of four-punctured spheres.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on Sobolev spaces on punctured Riemann surfaces with cylindrical ends.
-/

public section

open Filter Function Set MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped NNReal Manifold Real
open TauCeti.Complex (realChart)

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The linearized operator along the associativity family has finite-dimensional kernel on
`W^{1,2}`.** Let the Hamiltonians `H i`, `Hout`, `G` and `G'` be jointly `C²` of period one, let
`L > 4`, and let `K_τ` be the associativity family
`TauCeti.Floer.associativityPerturbation H Hout G G' L τ` at a parameter `τ`, a datum on the sphere
with the input ends of centers `c i` and scales `a i` of the associativity path of plumbing factor
`e^{-2πL} / 4` at `τ`. For each input end `i`, let `x i` be
an orbit of `H i` starting at a nondegenerate fixed point of its time-one map and let `J_e i` be a
`C¹` family of almost complex structures compatible along `x i`; for the output end, let `x_out`
and `J_out` be the same data for the Hamiltonian `H'(t, y) = -Hout(-t, y)` of the output end read
in its positive end chart. Let `J` be `J_e i (t)` beyond `s = 2` in the chart
`ψ_i = realChart (z ↦ c i + a i φ₀(z))` of each input end and `J_out (t)` beyond `s = 2` in the
positive end chart `φ'_∞` of the output end. Let `u` and `J` along `u` be `C¹` on the sphere minus
the centers `c i`, with `J` compatible along `u` there, let `u` solve the Floer equation of `K_τ`
beyond `s = 2` on each end, and let its loops in the end charts converge uniformly to the orbits
while the slice defects tend uniformly to zero. Then the realization `D_u : W^{1,2}_0 → L²` of the
linearized Floer operator of `K_τ` on the sphere minus the centers, for the weight
`movingEndsWeight c`, has finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_associativityPerturbation
    (ω : SymplecticForm V) {H : Fin 3 → ℝ → V → ℝ} {Hout G G' : ℝ → V → ℝ}
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContDiff ℝ 2 (uncurry G)) (hG' : Periodic G' 1) (hG's : ContDiff ℝ 2 (uncurry G'))
    {L : ℝ} (hL : 4 < L) (τ : ℝ) {Λ : Fin 3 → ℝ≥0}
    (hX : ∀ i, LipschitzWith (Λ i) (ω.timeDependentHamiltonianSuspension (H i)))
    {x : Fin 3 → ℝ → V} (hx : ∀ i t, HasDerivAt (x i) (ω.hamiltonianVectorField (H i t) (x i t)) t)
    (hnd : ∀ i, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (H i) (hX i) 0 1) (x i 0))
    {Je : Fin 3 → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ i t, ω.Compatible (Je i t (x i t))) {Λout : ℝ≥0}
    (hXout : LipschitzWith Λout (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {xout : ℝ → V}
    (hxout : ∀ t, HasDerivAt xout (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (xout t)) t)
    (hndout : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hXout 0 1) (xout 0))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJoutx : ∀ t, ω.Compatible (Jout t (xout t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ) =
        Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) → ContDiffAt ℝ 1 u z)
    (hc : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) → ω.Compatible (J z (u z)))
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
            associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ)
          (u (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
            associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ)))
        (ω.perturbedFDeriv
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            1)
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            Complex.I) u
          (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
            associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ) :
          ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) (s, t)))
      (x i) atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) (s, t))
      0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}
      (movingEndsWeight (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ))
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
        Complex.I) u).ker := by
  obtain ⟨ha, hsep, hout⟩ :=
    associativityScale_ne_zero_and_pairwise_add_le_norm_sub_and_norm_add_le (L := L) (by linarith) τ
  -- Far out on the ends the family is the datum of the moving input ends; on the core only its
  -- smoothness off the centers is used.
  exact finiteDimensional_ker_floerConformalSobolevOperator_of_movingEnds ω hH hHs hHout hHouts
    ha hsep hout hX hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq hJoutq
    (fun i ζ hζ ↦ associativityPerturbation_realChart_apply_one_eq_and_apply_I_eq (by linarith) hH
      i (by linarith))
    (fun ζ hζ ↦ associativityPerturbation_positiveEndChart_inf_apply_one_eq_and_apply_I_eq
      (by linarith) hHout (by linarith)) hJ
    (fun z hz ↦ contDiffAt_uncurry_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's
      hL hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's
      hL hz (u z) Complex.I) hu hc hF hFout hux hδ huxout hδout

/-- **The linearized operator along the associativity family has closed range on `W^{1,2}`.**
Under the hypotheses of
`finiteDimensional_ker_floerConformalSobolevOperator_associativityPerturbation`, the realization
`D_u : W^{1,2}_0 → L²` of the linearized Floer operator of the associativity family `K_τ` on the
sphere minus the centers, for the weight `movingEndsWeight c`, has closed range. -/
theorem isClosed_range_floerConformalSobolevOperator_associativityPerturbation
    (ω : SymplecticForm V) {H : Fin 3 → ℝ → V → ℝ} {Hout G G' : ℝ → V → ℝ}
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 2 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 2 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContDiff ℝ 2 (uncurry G)) (hG' : Periodic G' 1) (hG's : ContDiff ℝ 2 (uncurry G'))
    {L : ℝ} (hL : 4 < L) (τ : ℝ) {Λ : Fin 3 → ℝ≥0}
    (hX : ∀ i, LipschitzWith (Λ i) (ω.timeDependentHamiltonianSuspension (H i)))
    {x : Fin 3 → ℝ → V} (hx : ∀ i t, HasDerivAt (x i) (ω.hamiltonianVectorField (H i t) (x i t)) t)
    (hnd : ∀ i, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (H i) (hX i) 0 1) (x i 0))
    {Je : Fin 3 → ℝ → V → AlmostComplexStructure V}
    (hJe : ∀ i, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je i p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ i t, ω.Compatible (Je i t (x i t))) {Λout : ℝ≥0}
    (hXout : LipschitzWith Λout (ω.timeDependentHamiltonianSuspension fun t y ↦ -Hout (-t) y))
    {xout : ℝ → V}
    (hxout : ∀ t, HasDerivAt xout (ω.hamiltonianVectorField (fun y ↦ -Hout (-t) y) (xout t)) t)
    (hndout : IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (fun t y ↦ -Hout (-t) y) hXout 0 1) (xout 0))
    {Jout : ℝ → V → AlmostComplexStructure V}
    (hJout : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jout p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJoutx : ∀ t, ω.Compatible (Jout t (xout t))) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJeq : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      J (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ) =
        Je i ζ.2)
    (hJoutq : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → J (positiveEndChart inf ζ) = Jout ζ.2) {u : ℝ × ℝ → V}
    (hJ : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) → ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) → ContDiffAt ℝ 1 u z)
    (hc : ∀ z : ℝ × ℝ, (∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) → ω.Compatible (J z (u z)))
    (hF : ∀ i (ζ : ℝ × ℝ), 2 < ζ.1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
            associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ)
          (u (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
            associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ)))
        (ω.perturbedFDeriv
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            1)
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            Complex.I) u
          (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
            associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ) :
          ℝ × ℝ →ₗ[ℝ] V))
    (hFout : ∀ ζ : ℝ × ℝ, 2 < ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart inf ζ) (u (positiveEndChart inf ζ)))
      (ω.perturbedFDeriv
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u (positiveEndChart inf ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ i, TendstoUniformlyOn
      (fun s t ↦ u (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) (s, t)))
      (x i) atTop (Icc 0 1))
    (hδ : ∀ i, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (H i t))
      (u ∘ realChart fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) (s, t))
      0 atTop (Icc 0 1))
    (huxout : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart inf (s, t))) xout atTop
      (Icc 0 1))
    (hδout : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField fun y ↦ -Hout (-t) y) (u ∘ positiveEndChart inf) (s, t))
      0 atTop (Icc 0 1)) :
    IsClosed ((ω.floerConformalSobolevOperator
      {z | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}
      (movingEndsWeight (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ))
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
        Complex.I) u).range :
      Set (Lp V 2 (volume.restrict
        {z | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}))) := by
  obtain ⟨ha, hsep, hout⟩ :=
    associativityScale_ne_zero_and_pairwise_add_le_norm_sub_and_norm_add_le (L := L) (by linarith) τ
  -- Far out on the ends the family is the datum of the moving input ends; on the core only its
  -- smoothness off the centers is used.
  exact isClosed_range_floerConformalSobolevOperator_of_movingEnds ω hH hHs hHout hHouts
    ha hsep hout hX hx hnd hJe hJex hXout hxout hndout hJout hJoutx hJeq hJoutq
    (fun i ζ hζ ↦ associativityPerturbation_realChart_apply_one_eq_and_apply_I_eq (by linarith) hH
      i (by linarith))
    (fun ζ hζ ↦ associativityPerturbation_positiveEndChart_inf_apply_one_eq_and_apply_I_eq
      (by linarith) hHout (by linarith)) hJ
    (fun z hz ↦ contDiffAt_uncurry_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's
      hL hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's
      hL hz (u z) Complex.I) hu hc hF hFout hux hδ huxout hδout

end TauCeti.SymplecticForm
