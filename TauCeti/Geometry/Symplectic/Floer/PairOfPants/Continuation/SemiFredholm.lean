/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm

/-!
# The semi-Fredholm estimate of a pair of pants with continuation necks

Pair-of-pants products for two choices of end Hamiltonians are compared by gluing continuation
cylinders to the ends of the pair of pants `S = ℂ ∖ {0, 1}`. The datum of this gluing,
`TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`, is the pair-of-pants datum of the inner
Hamiltonians `G` on the pants side of necks placed at the positions `L_q`, a continuation datum from
`G_q` to `H_q` along each neck, and `H_q(t) dt` beyond it. Its solutions, for neck positions moving
along a path, form the one-parameter families of pairs of pants whose ends compare continuation maps
with pair-of-pants products, and their counts rest on the Fredholm theory of the linearized
operator `D_u` of this datum.

This file proves the semi-Fredholm estimate for `D_u`, for any neck positions, as the theorem
`exists_forall_le_mul_integral_floerLinearization_pairOfPantsContinuationPerturbation_add`
in the namespace `TauCeti.SymplecticForm`: when the ends of a solution `u` converge to
nondegenerate orbits of the outer Hamiltonians `H_q`, with almost complex structures cylindrical far
out on the ends and compatible along `u`, there are `C ≥ 0` and `T ≥ 0` such that

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`

for every `C²` section `ξ` with compact support in `S`. Beyond the height `2 + ∑_q |L_q|` on each
end, past every neck and collar, the datum is the pair-of-pants datum of `H`
(`TauCeti.Floer.pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_sum_le`), so this
is the semi-Fredholm estimate for Floer data that agree with the pair-of-pants data far out on the
ends (`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add`).
The constants depend on the neck positions; no estimate uniform along a family of necks is made.

For the same reason the formal adjoint `D_u^*`, whose kernel is the cokernel of `D_u`, satisfies the
semi-Fredholm estimate of the adjoint for data that agree with the pair-of-pants data far out on the
ends
(`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_add`):
for covector fields `η`, read in the end charts as `(0, 1)`-forms `η'_q`, and with the `L²` norm of
`D_u^* η` weighted by the inverse of the cylindrical weight `ρ`,

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²)`
`  + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`

(`exists_forall_le_mul_integral_floerLinearizationAdjoint_pairOfPantsContinuationPerturbation_add`).
This needs the end structures and `u` to be `C²` far out on the ends.

The same reduction applies to the realization of `D_u` on the Sobolev space `W^{1,2}_0(S, V)` of
the cylindrical metric, `TauCeti.SymplecticForm.floerConformalSobolevOperator` for the cylindrical
weight `TauCeti.Floer.cylindricalWeight`. Its coefficient field is essentially bounded and it
satisfies Peetre's estimate whenever the data agree with the pair-of-pants data far out on the ends
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.SemiFredholm`), so under the hypotheses of
the semi-Fredholm estimate it has finite-dimensional kernel
(`finiteDimensional_ker_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation`) and
closed range (`isClosed_range_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation`).
The finiteness of the cokernel and the Fredholm index are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3, on the Fredholm property of the linearized operator and
  on continuation maps.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants product and its compatibility with
  continuation maps.
-/

public section

open Set Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture TauCeti.Floer
open scoped NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The semi-Fredholm estimate along a pair of pants with continuation necks.** Let `G_q` and
`H_q` be jointly `C²` period-one Hamiltonians on the three ends of `S = ℂ ∖ {0, 1}`, the inner and
outer Hamiltonians of the pair-of-pants perturbation with continuation necks at the positions `L_q`
(`TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`). Suppose that the positive end
Hamiltonians `H'_q` of the outer Hamiltonians have globally Lipschitz suspended vector fields, and
let `x_q` be orbits of `H'_q` starting at nondegenerate fixed points of the time-one maps. Let
`J(z)` be a family of almost complex structures, `C¹` along `u`, that is cylindrical far out on each
end, `J(φ'_q(s, t)) = J_q(t)` for `s ≥ R₁` with `C¹` families `J_q` compatible along `x_q`. Let `u`
be a `C¹` map on `S`, along which `J` is compatible, that solves the Floer equation for this datum
beyond `R₁` on each end, whose loops in each positive end chart `φ'_q` converge uniformly to `x_q`
while the slice defects `∂t (u ∘ φ'_q) - X_{H'_q}` tend uniformly to zero. Then there are `C ≥ 0`
and `T ≥ 0` such that every `C²` section `ξ` with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`

for the linearized Floer operator `D_u` of the datum. -/
theorem exists_forall_le_mul_integral_floerLinearization_pairOfPantsContinuationPerturbation_add
    (ω : SymplecticForm V) {G H : Puncture → ℝ → V → ℝ} (hG : ∀ q, Periodic (G q) 1)
    (hH : ∀ q, Periodic (H q) 1) (hGs : ∀ q, ContDiff ℝ 2 (uncurry (G q)))
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (L : Puncture → ℝ) {Λ : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (ξ ∘ positiveEndChart q) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity ξ z ≤
        C * ((∫ z, ‖ω.floerLinearization (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I) u ξ z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖ξ z‖ ^ 2) := by
  -- Beyond the height `max R₁ (2 + ∑_q |L_q|)` on every end the datum is the pair-of-pants datum
  -- of `H`.
  exact ω.exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add hH
    hHs hX hx hnd hJe hJex (R₁ := max R₁ (2 + ∑ r, |L r|))
    (fun q ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ))
    (fun q _ _ hz ↦ pairOfPantsContinuationPerturbation_components_eq (le_max_right _ _) q hz) hJ
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) 1)
    (fun z hz ↦
      contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) Complex.I)
    hu hc (fun q z hz hR ↦ hF q z hz ((le_max_left _ _).trans hR)) hux hδ

/-- **The semi-Fredholm estimate of the formal adjoint along a pair of pants with continuation
necks.** Let `G_q` and `H_q` be jointly `C²` period-one Hamiltonians on the three ends of
`S = ℂ ∖ {0, 1}`, the inner and outer Hamiltonians of the pair-of-pants perturbation with
continuation necks at the positions `L_q`
(`TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`).
Suppose that the positive end Hamiltonians `H'_q` of the outer Hamiltonians have globally Lipschitz
suspended vector fields, and let `x_q` be orbits of `H'_q` starting at nondegenerate fixed points of
the time-one maps. Let `J(z)` be a family of almost complex structures, `C¹` along `u`, that is
cylindrical far out on each end, `J(φ'_q(s, t)) = J_q(t)` for `s ≥ R₁` with `C²` families `J_q`
compatible along `x_q`. Let `u` be a `C¹` map on `S`, along which `J` is compatible, that solves the
Floer equation for this datum beyond `R₁` on each end and is `C²` there, whose loops in each
positive end chart `φ'_q` converge uniformly to `x_q` while the slice defects
`∂t (u ∘ φ'_q) - X_{H'_q}` tend uniformly to zero. Then there are `C ≥ 0` and `T ≥ 0` such that
every `C²` covector field `η` with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s η'_q‖² + ‖∂t η'_q‖² + ‖η'_q‖²)`
`  + ∫_{S_T} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ ρ⁻¹ ‖D_u^* η‖² + ∫_{S_{T + 1}} ‖η‖²)`

for the formal adjoint `D_u^*` of the linearized Floer operator of the datum, whose kernel is the
cokernel of `D_u`. Here `η'_q` is `η` read in the chart of the end `q` as a `(0, 1)`-form
(`TauCeti.Floer.covectorPullback`), and `ρ` is the cylindrical weight. -/
theorem
    exists_forall_le_mul_integral_floerLinearizationAdjoint_pairOfPantsContinuationPerturbation_add
    (ω : SymplecticForm V) {G H : Puncture → ℝ → V → ℝ} (hG : ∀ q, Periodic (G q) 1)
    (hH : ∀ q, Periodic (H q) 1) (hGs : ∀ q, ContDiff ℝ 2 (uncurry (G q)))
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (L : Puncture → ℝ) {Λ : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hu₂ : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → ContDiffAt ℝ 2 u (positiveEndChart q ζ))
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, 0 ≤ T ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      HasCompactSupport η → tsupport η ⊆ thricePuncturedSphereReal →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (covectorPullback (positiveEndChart q)
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) u η) ζ) +
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation T, sobolevDensity η z ≤
        C * ((∫ z, (cylindricalWeight z)⁻¹ * ‖ω.floerLinearizationAdjoint
          (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I) u η z‖ ^ 2) +
          ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (T + 1), ‖η z‖ ^ 2) :=
  -- Beyond the height `max R₁ (2 + ∑_q |L_q|)` on every end the datum is the pair-of-pants datum
  -- of `H`.
  ω.exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearizationAdjoint_add hH
    hHs hX hx hnd hJe hJex (R₁ := max R₁ (2 + ∑ r, |L r|))
    (fun q ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ))
    (fun q _ _ hz ↦ pairOfPantsContinuationPerturbation_components_eq (le_max_right _ _) q hz) hJ
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) 1)
    (fun z hz ↦
      contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) Complex.I)
    hu (fun q ζ hζ ↦ hu₂ q ζ ((le_max_left _ _).trans hζ)) hc
    (fun q z hz hR ↦ hF q z hz ((le_max_left _ _).trans hR)) hux hδ

/-- **The linearized operator along a pair of pants with continuation necks has
finite-dimensional kernel on `W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_pairOfPantsContinuationPerturbation_add`, the
realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator of the pair-of-pants
datum with continuation necks at the positions `L_q`, for the cylindrical metric, has
finite-dimensional kernel. -/
theorem finiteDimensional_ker_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation
    (ω : SymplecticForm V) {G H : Puncture → ℝ → V → ℝ} (hG : ∀ q, Periodic (G q) 1)
    (hH : ∀ q, Periodic (H q) 1) (hGs : ∀ q, ContDiff ℝ 2 (uncurry (G q)))
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (L : Puncture → ℝ) {Λ : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).ker :=
  ω.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants hH hHs hX hx hnd hJe hJex
      (R₁ := max R₁ (2 + ∑ r, |L r|)) (fun q ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ))
      (fun q _ _ hz ↦ pairOfPantsContinuationPerturbation_components_eq (le_max_right _ _) q hz)
      hJ
      (fun z hz ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) 1)
      (fun z hz ↦
        contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) Complex.I)
      hu hc (fun q z hz hR ↦ hF q z hz ((le_max_left _ _).trans hR)) hux hδ

/-- **The linearized operator along a pair of pants with continuation necks has closed range on
`W^{1,2}`.** Under the hypotheses of the semi-Fredholm estimate
`exists_forall_le_mul_integral_floerLinearization_pairOfPantsContinuationPerturbation_add`, the
realization `D_u : W^{1,2}_0(S, V) → L²(S, V)` of the linearized Floer operator of the pair-of-pants
datum with continuation necks at the positions `L_q`, for the cylindrical metric, has closed range.
-/
theorem isClosed_range_floerConformalSobolevOperator_pairOfPantsContinuationPerturbation
    (ω : SymplecticForm V) {G H : Puncture → ℝ → V → ℝ} (hG : ∀ q, Periodic (G q) 1)
    (hH : ∀ q, Periodic (H q) 1) (hGs : ∀ q, ContDiff ℝ 2 (uncurry (G q)))
    (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q))) (L : Puncture → ℝ) {Λ : Puncture → ℝ≥0}
    (hX : ∀ q, LipschitzWith (Λ q)
      (ω.timeDependentHamiltonianSuspension (positiveEndHamiltonian H q)))
    {x : Puncture → ℝ → V}
    (hx : ∀ q t, HasDerivAt (x q)
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (x q t)) t)
    (hnd : ∀ q, IsNondegenerateFixedPt 𝓘(ℝ, V)
      (ω.timeDependentHamiltonianFlow (positiveEndHamiltonian H q) (hX q) 0 1) (x q 0))
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {Je : Puncture → ℝ → V → AlmostComplexStructure V} {R₁ : ℝ}
    (hJe : ∀ q, ContDiff ℝ 1 fun p : ℝ × V ↦ (Je q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJex : ∀ q t, ω.Compatible (Je q t (x q t)))
    (hJeq : ∀ q (ζ : ℝ × ℝ), R₁ ≤ ζ.1 → J (positiveEndChart q ζ) = Je q ζ.2)
    {u : ℝ × ℝ → V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ thricePuncturedSphereReal, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ thricePuncturedSphereReal, ω.Compatible (J z (u z)))
    (hF : ∀ q, ∀ z ∈ thricePuncturedSphereReal, R₁ ≤ (positiveEndCoord q z).1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z)) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hux : ∀ q, TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) (x q) atTop
      (Icc 0 1))
    (hδ : ∀ q, TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1)) :
    IsClosed ((ω.floerConformalSobolevOperator thricePuncturedSphereReal
      cylindricalWeight (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u).range : Set (Lp V 2 (volume.restrict thricePuncturedSphereReal))) :=
  ω.isClosed_range_floerConformalSobolevOperator_pairOfPants hH hHs hX hx hnd hJe hJex
      (R₁ := max R₁ (2 + ∑ r, |L r|)) (fun q ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ))
      (fun q _ _ hz ↦ pairOfPantsContinuationPerturbation_components_eq (le_max_right _ _) q hz)
      hJ
      (fun z hz ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) 1)
      (fun z hz ↦
        contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) Complex.I)
      hu hc (fun q z hz hR ↦ hF q z hz ((le_max_left _ _).trans hR)) hux hδ

end TauCeti.SymplecticForm
