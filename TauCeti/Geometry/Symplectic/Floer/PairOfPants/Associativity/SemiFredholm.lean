/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Associativity
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.SemiFredholm

/-!
# The semi-Fredholm estimate along the associativity family

The associativity of the pair-of-pants product compares the two compositions `(x₁ x₂) x₃` and
`x₁ (x₂ x₃)` through the one-parameter family of Floer data
`K_τ = TauCeti.Floer.associativityPerturbation H Hout G G' L τ`, `τ ∈ ℝ`, on spheres with three
moving input ends: the datum `Σ_τ` of the moving input ends along the associativity path
(`TauCeti.Floer.associativityCenter`, `TauCeti.Floer.associativityScale` of plumbing factor
`e^{-2πL} / 4`), plus the neck data of the two compositions switched on for `τ < 0` and for
`τ > 1`. The counts along this family rest on the Fredholm theory of the linearized Floer operator
`D_u` of `K_τ`, on a finite-dimensional symplectic vector space `(V, ω)`.

This file proves the semi-Fredholm estimate for `D_u` at every member `τ` of the family and every
neck length `L > 4`
(`exists_forall_le_mul_integral_floerLinearization_associativityPerturbation_add`, in the
namespace `TauCeti.SymplecticForm`): when the ends of a solution `u` converge to nondegenerate
orbits, with almost complex structures cylindrical far out on the ends and compatible along `u`,
there are `C ≥ 0` and `T ≥ 2` such that

`∑_i ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ_i)‖² + ‖∂t (ξ ∘ ψ_i)‖² + ‖ξ ∘ ψ_i‖²)`
`  + ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²)`
`  + ∫_{Σ_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{Σ_{T + 1}} ‖ξ‖²)`

for every `C²` section `ξ` with compact support in the sphere minus the three input punctures of
the configuration at `τ`. Here `ψ_i` is the chart `z ↦ c_i + a_i φ₀(z)` of the input end `i` of
that configuration, `φ'_∞` the positive end chart of the output end and `Σ_T` the truncation
`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation` at height `T`.

On the part `s > 0` of every input end and the part `s ≥ 1` of the output end the neck data
vanish, and `K_τ` is the datum `Σ_τ` of the moving input ends
(`associativityPerturbation_add_mul_cylindricalEndLift_eq_puncturedSpherePerturbation`,
`associativityPerturbation_cylindricalEndLift_inf_eq_puncturedSpherePerturbation`, in the
namespace `TauCeti.Floer`).
So the estimate is the case of the semi-Fredholm estimate
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds`
on spheres with moving input ends for Floer data that are `Σ_τ` far out on the ends. On the
compact core, where the necks sit, only the smoothness of `K_τ` off the input punctures is used
(`TauCeti.Floer.contDiffAt_uncurry_associativityPerturbation`).

The constants depend on `τ` and `L`; no estimate uniform along the family is made. The Sobolev
realization of `D_u`, the estimate of its formal adjoint and the Fredholm index are not treated
here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and the associativity of
  the product through families of four-punctured spheres.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate on punctured Riemann surfaces with cylindrical
  ends.
-/

public section

open Filter Function Set MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped NNReal Manifold Real
open TauCeti.Complex (realChart equivRealProdCLM_symm_realChart)

namespace TauCeti.SymplecticForm

open Floer

section Charts

variable {M : Type*} {H : Fin 3 → ℝ → M → ℝ} {Hout G G' : ℝ → M → ℝ} {L : ℝ} {τ : ℝ}

/-- On the part `s > 0` of the input end `i`, read in the chart `ψ_i` of the configuration at
`τ`, the associativity family is the datum of the moving input ends. -/
private theorem associativityPerturbation_realChart_eq (hL : 2 < L)
    (hH : ∀ i, Periodic (H i) 1) (i : Fin 3) {ζ : ℝ × ℝ} (hζ : 0 < ζ.1) :
    associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm
        (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
          associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ)) =
      puncturedSpherePerturbation (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) H Hout
        (Complex.equivRealProdCLM.symm
          (realChart (fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
            associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z)
            ζ)) := by
  funext y
  rw [equivRealProdCLM_symm_realChart]
  exact associativityPerturbation_add_mul_cylindricalEndLift_eq_puncturedSpherePerturbation hL τ
    (hH i) (by simpa using hζ) y

/-- On the part `s ≥ 1` of the output end, read in the positive end chart `φ'_∞`, the
associativity family is the datum of the moving input ends. -/
private theorem associativityPerturbation_positiveEndChart_inf_eq (hL : 2 < L)
    (hHout : Periodic Hout 1) {ζ : ℝ × ℝ} (hζ : 1 ≤ ζ.1) :
    associativityPerturbation H Hout G G' L τ
        (Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)) =
      puncturedSpherePerturbation (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) H Hout
        (Complex.equivRealProdCLM.symm (positiveEndChart inf ζ)) := by
  funext y
  rw [positiveEndChart_apply, equivRealProdCLM_symm_endChart]
  refine associativityPerturbation_cylindricalEndLift_inf_eq_puncturedSpherePerturbation hL τ hHout
    ?_ y
  simpa only [endSign_inf, Complex.equivRealProdCLM_symm_apply_re, Prod.smul_fst, smul_eq_mul,
    neg_one_mul, neg_le_neg_iff] using hζ

end Charts

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The semi-Fredholm estimate along the associativity family.** Let the Hamiltonians `H i`,
`Hout`, `G` and `G'` be jointly `C²` of period one, let `L > 4`, and let `K_τ` be the associativity
family `TauCeti.Floer.associativityPerturbation H Hout G G' L τ` at a parameter `τ`, a datum on the
sphere with the input ends of centers `c i` and scales `a i` of the associativity path of plumbing
factor `e^{-2πL} / 4` at `τ`. For each input end `i`, let `x i` be an orbit of `H i` starting at a
nondegenerate fixed point of its time-one map and let `J_e i` be a `C¹` family of almost complex
structures compatible along `x i`; for the output end, let `x_out` and `J_out` be the same data for
the Hamiltonian `H'(t, y) = -Hout(-t, y)` of the output end read in its positive end chart. Let `J`
be `J_e i (t)` beyond `s = 2` in the chart `ψ_i = realChart (z ↦ c i + a i φ₀(z))` of each input
end and `J_out (t)` beyond `s = 2` in the positive end chart `φ'_∞` of the output end. Let `u` and
`J` along `u` be `C¹` on the sphere minus the centers `c i`, with `J` compatible along `u` there,
let `u` solve the Floer equation of `K_τ` beyond `s = 2` on each end, and let its loops in the end
charts converge uniformly to the orbits while the slice defects tend uniformly to zero. Then there
are `C ≥ 0` and `T ≥ 2` such that every `C²` section `ξ` with compact support in the sphere minus
the centers satisfies

`∑_i ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ ψ_i)‖² + ‖∂t (ξ ∘ ψ_i)‖² + ‖ξ ∘ ψ_i‖²)`
`  + ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_∞)‖² + ‖∂t (ξ ∘ φ'_∞)‖² + ‖ξ ∘ φ'_∞‖²)`
`  + ∫_{Σ_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{Σ_{T + 1}} ‖ξ‖²)`

for the linearized Floer operator `D_u` of `K_τ`, where `Σ_T` is the truncation
`TauCeti.ThricePuncturedSphere.puncturedSphereTruncation c a T`. -/
theorem exists_forall_le_mul_integral_floerLinearization_associativityPerturbation_add
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
    ∃ C, 0 ≤ C ∧ ∃ T, 2 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ {z | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i} →
      (∑ i, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity
          (ξ ∘ realChart fun z ↦ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
            associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) ζ) +
        (∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart inf) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation
            (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
            (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) T,
          sobolevDensity ξ z ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            1)
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            Complex.I) u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation
              (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
              (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) (T + 1),
            ‖ξ z‖ ^ 2) :=
  have hf := exp_neg_two_pi_mul_div_four_pos_and_three_mul_le_one (show 0 ≤ L by linarith)
  -- Far out on the ends the family is the datum of the moving input ends; on the core only its
  -- smoothness off the centers is used.
  exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add_of_movingEnds
    ω hH hHs hHout hHouts (associativityScale_ne_zero hf.1 τ)
    (pairwise_add_le_norm_associativityCenter_sub hf.1.le hf.2 τ)
    (norm_associativityCenter_add_le hf.1.le (by linarith) τ) hX hx hnd hJe hJex hXout hxout hndout
    hJout hJoutx hJeq hJoutq
    (fun i ζ hζ ↦ by
      rw [associativityPerturbation_realChart_eq (G := G) (G' := G') (L := L) (by linarith) hH i
        (by linarith)]
      exact ⟨rfl, rfl⟩)
    (fun ζ hζ ↦ by
      rw [associativityPerturbation_positiveEndChart_inf_eq (H := H) (G := G) (G' := G') (L := L)
        (by linarith) hHout (by linarith)]
      exact ⟨rfl, rfl⟩) hJ
    (fun z hz ↦ contDiffAt_uncurry_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's
      hL hz (u z) 1)
    (fun z hz ↦ contDiffAt_uncurry_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's
      hL hz (u z) Complex.I) hu hc hF hFout hux hδ huxout hδout

end TauCeti.SymplecticForm
