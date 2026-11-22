/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm

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
`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_continuation_add`
in the namespace `TauCeti.SymplecticForm`: when the ends of a solution `u` converge to
nondegenerate orbits of the outer Hamiltonians `H_q`, with almost complex structures cylindrical far
out on the ends and compatible along `u`, there are `C ≥ 0` and `T ≥ 0` such that

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`

for every `C²` section `ξ` with compact support in `S`. Beyond the height `2 + ∑_q |L_q|` on each
end, past every neck and collar, the datum is the pair-of-pants datum of `H`
(`TauCeti.Floer.pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_le`), so this is
the semi-Fredholm estimate for Floer data that agree with the pair-of-pants data far out on the ends
(`exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add`).
The constants depend on the neck positions; no estimate uniform along a family of necks is made.

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
be a `C¹` solution on `S` of the Floer equation for this datum, along which `J` is compatible, whose
loops in each positive end chart `φ'_q` converge uniformly to `x_q` while the slice defects
`∂t (u ∘ φ'_q) - X_{H'_q}` tend uniformly to zero. Then there are `C ≥ 0` and `T ≥ 0` such that
every `C²` section `ξ` with compact support in `S` satisfies

`∑_q ∫_{(T, ∞) × [0, 1]} (‖∂s (ξ ∘ φ'_q)‖² + ‖∂t (ξ ∘ φ'_q)‖² + ‖ξ ∘ φ'_q‖²)`
`  + ∫_{S_T} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{S_{T + 1}} ‖ξ‖²)`

for the linearized Floer operator `D_u` of the datum. -/
theorem
  exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_continuation_add
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
    (hF : ∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J z (u z)) (ω.perturbedFDeriv
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
  set R := max R₁ (2 + ∑ r, |L r|)
  -- Beyond the height `R` on every end the datum is the pair-of-pants datum of `H`.
  have hK (q : Puncture) (z : ℝ × ℝ) (hz : R ≤ (positiveEndCoord q z).1) (y : V) :
      pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) y =
        pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y := by
    have hLq : L q ≤ ∑ r, |L r| := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun r ↦ |L r|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ q))
    have hsum : 0 ≤ ∑ r, |L r| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    rw [fst_positiveEndCoord] at hz
    have hR : 2 + ∑ r, |L r| ≤ R := le_max_right _ _
    exact pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_le (by linarith)
      (by linarith) y
  exact ω.exists_forall_sum_setIntegral_add_setIntegral_le_mul_integral_floerLinearization_add hH
    hHs hX hx hnd hJe hJex (R₁ := R) (fun q ζ hζ ↦ hJeq q ζ ((le_max_left _ _).trans hζ))
    (fun q z _ hz ↦ ⟨funext fun y ↦ congrArg (· 1) (hK q z hz y),
      funext fun y ↦ congrArg (· Complex.I) (hK q z hz y)⟩) hJ
    (fun z hz ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) 1)
    (fun z hz ↦
      contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz (u z) Complex.I)
    hu hc hF hux hδ

end TauCeti.SymplecticForm
