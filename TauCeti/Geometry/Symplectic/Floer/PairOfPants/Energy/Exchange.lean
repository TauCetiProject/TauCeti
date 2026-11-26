/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Recentring
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# The energy of the input-exchange family

Graded commutativity of the pair-of-pants product is proved with the input-exchange family
`K_c = TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`, of perturbation data on
`S = ℂ ∖ {0, 1}`: the input part of the pair-of-pants datum plus the negative plane datum of the
output Hamiltonian translated by `c`, so that the output end of `K_c` is the end at `∞` recentred at
`c`. A one-parameter family of moduli spaces gives a chain homotopy whose kernel must be supported
in the sense of `TauCeti.NovikovModule.kernelProduct`, and this support comes from an action bound
that is uniform in `c`. This file proves the energy identity of every member of the family and the
resulting action and energy bounds, all with the same constants as for the pair of pants.

Write `ℓ_q(R)(t) = u(φ_q(R + i t))` for the loops of a map `u` along the circles `s = R` of the
input ends `q ∈ {0, 1}`, and `ℓ^c_∞(R)(t) = u(c + φ_∞(-R + i t))` for its loop along the circle
`s = -R` of the recentred output end. These circles bound the truncation
`TauCeti.ThricePuncturedSphere.exchangeTruncation c R`. For a map `u` which is `C²` on `S`,
period-one `C¹` Hamiltonians `H_q` on a symplectic vector space and `R ≥ 2`, the Floer energy of
`u` for `K_c` over this truncation is

`∫ E = A_{H_0}(ℓ_0(R)) + A_{H_1}(ℓ_1(R)) - A_{H_∞}(ℓ^c_∞(R)) - ∫_S R_{K_c}(u)`

(`SymplecticForm.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation`), where
`A_H` is the Hamiltonian action `TauCeti.SymplecticForm.hamiltonianAction`. For `c = 0` this is the
energy identity of the pair of pants
(`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction`).
Since `K_c` is the pullback of `K_0` along `Φ_c`
(`TauCeti.Floer.perturbationPullback_exchangeMap_exchangePerturbation`), the curvature of `K_c`
along `u` is that of `K_0` along `u ∘ Φ_c`, and the curvature bound
`TauCeti.SymplecticForm.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le` shows that
the energy differs from the change of action by at most `B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`
(`SymplecticForm.abs_integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation_sub_le`).
For a solution of the Floer equation with tame almost complex structures the energy is
nonnegative, which gives the action bound `A_{H_∞}(ℓ^c_∞(R)) ≤ A_{H_0}(ℓ_0(R)) + A_{H_1}(ℓ_1(R))
+ B₀ + B₁ + B_∞` (`SymplecticForm.hamiltonianAction_le_add_add_sum_of_exchangePerturbation`) and its
limit `a_∞ ≤ a_0 + a_1 + B₀ + B₁ + B_∞` for the limiting actions of the ends
(`SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_exchangePerturbation`). As for the
pair of pants, the constant can be replaced by the one-sided constant
`-∫₀¹ h_0 - ∫₀¹ h_1 + ∫₀¹ h_∞` for functions of time with `h_q ≤ H_q` on the inputs and
`H_∞ ≤ h_∞` on the output, which transforms correctly under a change of normalization of the
Hamiltonians (`SymplecticForm.hamiltonianAction_le_add_add_sub_sum_of_exchangePerturbation`,
`SymplecticForm.le_add_add_sub_sum_of_tendsto_hamiltonianAction_exchangePerturbation`).

The truncations with recentred output end increase with `R` and exhaust `S`, so for a Floer
solution whose boundary actions converge to `a_q` monotone convergence gives the energy over the
whole of `S`,

`E(u) = a_0 + a_1 - a_∞ - ∫_S R_{K_c}(u)`

(`SymplecticForm.lintegral_floerEnergyDensity_exchangePerturbation_eq`). In particular the energy
is finite and at most `a_0 + a_1 - a_∞ + B₀ + B₁ + B_∞`, uniformly in `c ∈ [0, 1]`
(`SymplecticForm.lintegral_floerEnergyDensity_exchangePerturbation_le`, with the one-sided form
`SymplecticForm.lintegral_floerEnergyDensity_exchangePerturbation_le_sub_sum`). This is the
energy bound with which Gromov–Floer compactness applies to the solutions of the whole family.

The same identities hold for a map `u` which is `C¹` on `S`, with values in a finite-dimensional
manifold `M` carrying a nondegenerate two-form `ω`, such as a closed symplectic manifold. There the
actions of the boundary loops are not defined without caps, and the identity is stated, as for the
pair of pants
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`),
through the symplectic area and the Hamiltonian boundary terms: for `R ≥ 1`, over the truncation
`T` with recentred output end,

`∫_T E = ∫_T u^*ω + β(R - 1) (∫₀¹ H_0(t, ℓ_0(R)(t)) dt + ∫₀¹ H_1(t, ℓ_1(R)(t)) dt
  - ∫₀¹ H_∞(t, ℓ^c_∞(R)(t)) dt) - ∫_T R_{K_c}(u)`

(`IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation` in
`SmoothTwoForm`), with `β = smoothTransition`. So the energy differs from the area plus the
boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in `c` and `R`, and for a Floer solution with
tame almost complex structures on the truncation, `R ≥ 2`, the area plus the boundary terms is at
least `-(B₀ + B₁ + B_∞)`
(`IsNondegenerate.neg_sum_le_integral_add_of_exchangePerturbation_exchangeTruncation` in
`SmoothTwoForm`). If the boundary loops converge
pointwise to loops `x_q` and the energy and area densities are integrable over `S`, then on the
whole of `S`

`∫_S E = ∫_S u^*ω + ∫₀¹ H_0(t, x_0(t)) dt + ∫₀¹ H_1(t, x_1(t)) dt - ∫₀¹ H_∞(t, x_∞(t)) dt
  - ∫_S R_{K_c}(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation`). For a Floer
solution with tame almost complex structures the energy is nonnegative, so the area plus the
Hamiltonian terms at the asymptotic orbits is at least `-(B₀ + B₁ + B_∞)`, uniformly in `c`
(`IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap_exchangePerturbation` in
`SmoothTwoForm`), and if the area plus these terms is at most `A`, then the energy over every part
of `S` is at most `A + B₀ + B₁ + B_∞`
(`IsNondegenerate.setIntegral_floerEnergyDensity_exchangePerturbation_le` in `SmoothTwoForm`).
Once the area is expressed through the actions of capped orbits and the class of
the solution, this becomes the lower bound on the valuation of the output monomials of the
commutativity homotopy on a closed symplectic manifold.

The member `c` of the family is the pullback of the pair-of-pants datum `K_0` along the
orientation-preserving diffeomorphism `Φ_c` of the plane (`TauCeti.Floer.exchangeMap`), which is
the identity near the input ends, where `K_c = K_0`, and the translation by `c` near the output
end, where `K_c` is the translate of `K_0`; in between both data vanish. The energy, area and
curvature integrals are transported along `Φ_c` by
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Recentring`, so the energy identity of the
pair of pants for `u ∘ Φ_c` is the energy identity of `K_c` for `u`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product and its energy
  estimate.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology NNReal Manifold

namespace TauCeti

namespace Floer

/-! ### The family as a pullback of the pair-of-pants datum -/

section Datum

variable {M : Type*} {H : Puncture → ℝ → M → ℝ} {c : ℝ}

/-- **The member `c` of the family is the pullback of the pair-of-pants datum along `Φ_c`.** For
`0 ≤ c ≤ 1`, the pullback along `Φ_c` (`TauCeti.Floer.exchangeMap`) of the member `c` of the
input-exchange family is the pair-of-pants datum, its member `0`. -/
theorem perturbationPullback_exchangeMap_exchangePerturbation (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (v y : ℝ × ℝ) (x : M) :
    perturbationPullback (exchangeMap c)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) v y x =
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm y) x
        (Complex.equivRealProdCLM.symm v) :=
  perturbationPullback_exchangeMap_of_eq hc₀ hc₁
    (fun _ hw ↦ funext (exchangePerturbation_of_norm_le hc₀ hc₁ hw))
    (fun _ h₁ h₂ ↦ funext (exchangePerturbation_eq_zero hc₀ hc₁ h₁ h₂))
    (fun _ h₁ h₂ ↦ by
      rw [← exchangePerturbation_zero]
      exact funext (exchangePerturbation_eq_zero le_rfl zero_le_one (by simpa using h₁)
        (by simpa using h₂)))
    (fun _ hw ↦ funext (exchangePerturbation_add hc₀ hc₁ hw)) v y x

end Datum

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Puncture → ℝ → M → ℝ} {c : ℝ}

variable [IsManifold I ⊤ M] {ω : SmoothTwoForm I M}

variable [FiniteDimensional ℝ E]

/-- **The energy identity of the input-exchange family, for a manifold target.** Let `K_c` be the
member `c ∈ [0, 1]` of the input-exchange family of period-one `C¹` Hamiltonians `H_q` on a
finite-dimensional manifold with a nondegenerate two-form, such as a closed symplectic manifold,
with components `K_s(z) = K_c(z)(1)` and `K_t(z) = K_c(z)(i)` in the global coordinate
`z = s + i t` of `ℂ`, and let `u` be a map which is `C¹` on `S = ℂ ∖ {0, 1}`. For `R ≥ 1`, the Floer
energy of `u` over the truncation `T` of `S` with output end recentred at `c` is the symplectic
area, plus `β(R - 1)` times the Hamiltonian terms along the boundary circles of `T`, minus the
integrated curvature:

`∫_T E = ∫_T u^*ω + β(R - 1) (∫₀¹ H_0(t, ℓ_0(t)) dt + ∫₀¹ H_1(t, ℓ_1(t)) dt
  - ∫₀¹ H_∞(t, ℓ^c_∞(t)) dt) - ∫_T R_{K_c}(u)`.

Here `ℓ_q(t) = u(φ_q(R + i t))` are the loops along the circles `s = R` of the input ends,
`ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` is the loop along the circle `s = -R` of the recentred output
end, and `β = smoothTransition`, so `β(R - 1) = 1` for `R ≥ 2`. For `c = 0` this is
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * ((∫ t in (0 : ℝ)..1, H zero t (u (Complex.equivRealProdCLM
            (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) +
          (∫ t in (0 : ℝ)..1, H one t (u (Complex.equivRealProdCLM
            (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, H inf t (u (Complex.equivRealProdCLM
            (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hK := contMDiffAt_exchangePerturbation_apply hH hHs c
  have hp := perturbationPullback_exchangeMap_exchangePerturbation (H := H) hc₀ hc₁
  -- The map `u ∘ Φ_c` is `C¹` on `S`, and the energy identity of the pair of pants applies to it.
  have hv := contMDiffOn_comp_exchangeMap hc₀ hc₁ hu
  have hs := measurableSet_preimage_truncation R
  have hsS := preimage_truncation_subset_thricePuncturedSphereReal R
  rw [← image_exchangeMap_truncation hc₀ hc₁ hR,
    ω.integral_floerEnergyDensity_image_exchangeMap hK hp hc₀ hc₁ hu hs hsS,
    integral_area_image_exchangeMap ω hc₀ hc₁ hu hs hsS,
    ω.integral_hamiltonianCurvature_image_exchangeMap hK hp hc₀ hc₁ u hs hsS,
    hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs
      isOpen_thricePuncturedSphereReal hsS hv hR]
  -- The boundary loops of `u ∘ Φ_c` are those of `u` on the recentred ends.
  simp only [Puncture.sum_univ, endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul,
    comp_apply, exchangeMap_cylindricalEndLift c (q := zero) (by decide) (by linarith : 0 ≤ R),
    exchangeMap_cylindricalEndLift c (q := one) (by decide) (by linarith : 0 ≤ R),
    exchangeMap_cylindricalEndLift_inf c hR]
  ring

/-- **The energy bound on truncations along the input-exchange family, for a manifold target.** If
the end Hamiltonians are bounded, `|H_q| ≤ B_q`, then for every `c ∈ [0, 1]` and `R ≥ 1` the Floer
energy of `u` for the member `c` of the family over the truncation with recentred output end
differs from the symplectic area plus the Hamiltonian boundary terms by at most `B₀ + B₁ + B_∞`,
uniformly in `c` and `R`. -/
theorem
    IsNondegenerate.abs_integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * ((∫ t in (0 : ℝ)..1, H zero t (u (Complex.equivRealProdCLM
            (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) +
          (∫ t in (0 : ℝ)..1, H one t (u (Complex.equivRealProdCLM
            (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, H inf t (u (Complex.equivRealProdCLM
            (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  have hK := contMDiffAt_exchangePerturbation_apply hH hHs c
  have hp := perturbationPullback_exchangeMap_exchangePerturbation (H := H) hc₀ hc₁
  have hsub (a b d : ℝ) : a + b - d - a - b = -d := by ring
  have hs := measurableSet_preimage_truncation R
  have hsS := preimage_truncation_subset_thricePuncturedSphereReal R
  rw [hω.integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation hH hHs hc₀ hc₁ hu hR,
    hsub, abs_neg, ← image_exchangeMap_truncation hc₀ hc₁ hR,
    ω.integral_hamiltonianCurvature_image_exchangeMap hK hp hc₀ hc₁ u hs hsS]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB _ _

/-- **The topological energy of a solution along the input-exchange family is bounded below on
truncations, for a manifold target.** Let `u` be `C¹` on `S = ℂ ∖ {0, 1}` and solve the Floer
equation `(du - X_{K_c})^{0,1} = 0` for the member `c ∈ [0, 1]` of the family on the truncation with
recentred output end, `R ≥ 2`, for almost complex structures `J z` on the tangent spaces
`T_{u(z)} M` tamed by the two-form. If `|H_q| ≤ B_q`, then since the energy is nonnegative, the
symplectic area over the truncation plus the boundary terms of the loops `ℓ_q(t) = u(φ_q(R + i t))`
of the input ends and `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` of the recentred output end is at least
`-(B₀ + B₁ + B_∞)`:

`-(B₀ + B₁ + B_∞) ≤ ∫_T u^*ω + ∫₀¹ H_0(t, ℓ_0(t)) dt + ∫₀¹ H_1(t, ℓ_1(t)) dt
  - ∫₀¹ H_∞(t, ℓ^c_∞(t)) dt`,

uniformly in `c` and `R`. -/
theorem IsNondegenerate.neg_sum_le_integral_add_of_exchangePerturbation_exchangeTruncation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 2 ≤ R)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R,
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -∑ q, B q ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∫ t in (0 : ℝ)..1, H zero t (u (Complex.equivRealProdCLM
            (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) +
          (∫ t in (0 : ℝ)..1, H one t (u (Complex.equivRealProdCLM
            (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, H inf t (u (Complex.equivRealProdCLM
            (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) := by
  have hpos := setIntegral_nonneg (μ := volume) (measurableSet_preimage_exchangeTruncation c R)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := abs_le.1
    (hω.abs_integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation_sub_le hH hHs hB
      hc₀ hc₁ hu (by linarith : (1 : ℝ) ≤ R))
  rw [smoothTransition.one_of_one_le (by linarith), one_mul] at h
  linarith [h.2]

/-- **The energy identity along the input-exchange family, for a manifold target.** Let `K_c` be
the member `c ∈ [0, 1]` of the input-exchange family of bounded period-one `C¹` Hamiltonians `H_q`
on a finite-dimensional manifold with a nondegenerate two-form. Let `u` be a map which is `C¹` on
`S`, whose loops `t ↦ u(φ_q(R + i t))` along the circles of the input ends `q ∈ {0, 1}` and
`t ↦ u(c + φ_∞(-R + i t))` along the circles of the recentred output end converge pointwise to
loops `x_q` as `R → ∞`, and whose Floer energy density for `K_c` and symplectic area density are
integrable over `S`. Then

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_{K_c}(u)`,

with the sign `+` on the input ends and `-` on the output end, as for the pair of pants
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`). -/
theorem IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {x : Puncture → ℝ → M}
    (hx : ∀ q ≠ inf, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hxinf : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (x inf t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hK := contMDiffAt_exchangePerturbation_apply hH hHs c
  have hp := perturbationPullback_exchangeMap_exchangePerturbation (H := H) hc₀ hc₁
  -- Transport everything along `Φ_c`, which maps `S` onto itself, to the map `u ∘ Φ_c` and the
  -- pair-of-pants datum.
  have hv := contMDiffOn_comp_exchangeMap hc₀ hc₁ hu
  have hs := isOpen_thricePuncturedSphereReal.measurableSet
  have himage := image_exchangeMap_thricePuncturedSphereReal hc₀ hc₁
  rw [← himage] at hE hA
  have hEv := integrableOn_of_integrableOn_image_exchangeMap hc₀ hc₁ hs hE
    fun w hw ↦ ω.floerEnergyDensity_comp_exchangeMap hK hp hc₀ hc₁ hu hw
  have hAv := integrableOn_of_integrableOn_image_exchangeMap hc₀ hc₁ hs hA
    fun w hw ↦ ω.eval₂_mfderiv_comp_stdComplexLine
      ((contDiff_exchangeMap c).differentiable two_ne_zero w)
      (mdifferentiableAt_exchangeMap hc₀ hc₁ hu hw)
  -- The end loops of `u ∘ Φ_c` are eventually those of `u` on the recentred ends.
  have hxv (q : Puncture) (t : ℝ) : Tendsto (fun R : ℝ ↦ (u ∘ exchangeMap c)
      (Complex.equivRealProdCLM (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))
      atTop (𝓝 (x q t)) := by
    rcases eq_or_ne q inf with rfl | hq
    · refine (hxinf t).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with R hR
      simp only [endSign_inf, neg_one_mul, comp_apply, exchangeMap_cylindricalEndLift_inf c hR]
    · have hsign : q.endSign = 1 := by
        cases q <;> simp_all
      refine (hx q hq t).congr' ?_
      filter_upwards [eventually_ge_atTop 0] with R hR
      simp only [hsign, one_mul, comp_apply, exchangeMap_cylindricalEndLift c hq hR]
  rw [← himage, ω.integral_floerEnergyDensity_image_exchangeMap hK hp hc₀ hc₁ hu hs subset_rfl,
    integral_area_image_exchangeMap ω hc₀ hc₁ hu hs subset_rfl,
    ω.integral_hamiltonianCurvature_image_exchangeMap hK hp hc₀ hc₁ u hs subset_rfl]
  exact hω.integral_floerEnergyDensity_pairOfPantsPerturbation hH hHs hB hv hxv hEv hAv

/-- **The energy bound along the input-exchange family, for a manifold target.** Under the
hypotheses of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation`,
the Floer energy over `S` differs from its topological part, the symplectic area plus the
Hamiltonian terms at the asymptotic orbits, by at most `B₀ + B₁ + B_∞`, uniformly in `c`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_exchangePerturbation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {x : Puncture → ℝ → M}
    (hx : ∀ q ≠ inf, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hxinf : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (x inf t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    |(∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z) -
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)| ≤ ∑ q, B q := by
  have hK := contMDiffAt_exchangePerturbation_apply hH hHs c
  have hp := perturbationPullback_exchangeMap_exchangePerturbation (H := H) hc₀ hc₁
  have hsub (a b d : ℝ) : a + b - d - a - b = -d := by ring
  rw [hω.integral_floerEnergyDensity_exchangePerturbation hH hHs hB hc₀ hc₁ hu hx hxinf hE hA,
    hsub, abs_neg, ← image_exchangeMap_thricePuncturedSphereReal hc₀ hc₁,
    ω.integral_hamiltonianCurvature_image_exchangeMap hK hp hc₀ hc₁ u
      isOpen_thricePuncturedSphereReal.measurableSet subset_rfl]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB _ _

/-- **The topological energy along the input-exchange family is bounded below, for a manifold
target.** Let `u` solve the Floer equation `(du - X_{K_c})^{0,1} = 0` on `S` for the member
`c ∈ [0, 1]` of the family, for almost complex structures `J z` on the tangent spaces `T_{u(z)} M`
tamed by the two-form, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation`. Since its energy
is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic orbits is at least
`-(B₀ + B₁ + B_∞)`, uniformly in `c`. -/
theorem IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap_exchangePerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {x : Puncture → ℝ → M}
    (hx : ∀ q ≠ inf, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hxinf : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (x inf t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -∑ q, B q ≤
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  have hpos := setIntegral_nonneg (μ := volume) isOpen_thricePuncturedSphereReal.measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := abs_le.1 (hω.abs_integral_floerEnergyDensity_exchangePerturbation_sub_le hH hHs hB hc₀
    hc₁ hu hx hxinf hE hA)
  linarith [h.2]

/-- **A solution of bounded topological energy has bounded energy over every part of `S`, along
the input-exchange family, for a manifold target.** Let `u` solve the Floer equation on `S` for the
member `c ∈ [0, 1]` of the family, for almost complex structures tamed by the two-form, under the
hypotheses of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation`,
with symplectic area plus the Hamiltonian terms at the asymptotic orbits at most `A`. Then over
every subset `Ω ⊆ S` the energy is at most `A + B₀ + B₁ + B_∞`, uniformly in `c`; this is the
energy bound that compactness of the family consumes. -/
theorem IsNondegenerate.setIntegral_floerEnergyDensity_exchangePerturbation_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {x : Puncture → ℝ → M}
    (hx : ∀ q ≠ inf, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hxinf : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (x inf t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    {A : ℝ}
    (htop : (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) ≤ A)
    {Ω : Set (ℝ × ℝ)} (hΩ : Ω ⊆ thricePuncturedSphereReal) :
    ∫ z in Ω, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z ≤
      A + ∑ q, B q := by
  have habs := hω.abs_integral_floerEnergyDensity_exchangePerturbation_sub_le hH hHs hB hc₀ hc₁
    hu hx hxinf hE hA
  refine (hω.setIntegral_floerEnergyDensity_mono_set hΩ
    isOpen_thricePuncturedSphereReal.measurableSet hE hJ hfloer).trans ?_
  linarith [(abs_sub_le_iff.1 habs).1]

end SmoothTwoForm

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {c : ℝ}

/-- The energy of `u` for `K_c` over the truncation with recentred output end is the energy of
`u ∘ Φ_c` for the pair-of-pants datum over the truncation `S_R`. -/
private theorem integral_floerEnergyDensity_exchangeTruncation_eq (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {R : ℝ}
    (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ exchangeMap c) z := by
  rw [← image_exchangeMap_truncation hc₀ hc₁ hR]
  simpa only [floerEnergyDensity_constSmooth] using
    ω.constSmooth.integral_floerEnergyDensity_image_exchangeMap
      (Floer.contMDiffAt_exchangePerturbation_apply hH
        (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) c)
      (perturbationPullback_exchangeMap_exchangePerturbation hc₀ hc₁) hc₀ hc₁
      (contMDiffOn_iff_contDiffOn.mpr (hu.of_le one_le_two))
      (measurableSet_preimage_truncation R) (preimage_truncation_subset_thricePuncturedSphereReal R)

/-- The integrated curvature of `K_c` along `u` is that of the pair-of-pants datum along
`u ∘ Φ_c`. -/
private theorem integral_hamiltonianCurvature_exchangePerturbation_eq (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) (u : ℝ × ℝ → V) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z ((u ∘ exchangeMap c) z) := by
  conv_lhs => rw [← image_exchangeMap_thricePuncturedSphereReal hc₀ hc₁]
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.integral_hamiltonianCurvature_image_exchangeMap
      (Floer.contMDiffAt_exchangePerturbation_apply hH
        (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) c)
      (perturbationPullback_exchangeMap_exchangePerturbation hc₀ hc₁) hc₀ hc₁ u
      isOpen_thricePuncturedSphereReal.measurableSet subset_rfl

/-- **The energy identity of the input-exchange family.** Let `K_c` be the member `c ∈ [0, 1]`
of the input-exchange family of period-one `C¹` Hamiltonians `H_q`, with components
`K_s(z) = K_c(z)(1)` and `K_t(z) = K_c(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let
`u` be a map which is `C²` on `S = ℂ ∖ {0, 1}`. For `R ≥ 2`, the Floer energy of `u` over the
truncation of `S` with output end recentred at `c` is the change of action between the loops
`ℓ_q(t) = u(φ_q(R + i t))` along the boundary circles of the input ends and the loop
`ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` along the boundary circle of the recentred output end, minus the
integrated curvature over `S`:

`∫ E = A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) - A_{H_∞}(ℓ^c_∞) - ∫_S R_{K_c}(u)`. -/
theorem integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
          (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- The map `u ∘ Φ_c` is `C²` on `S`, and the energy identity of the pair of pants applies to it.
  have hv : ContDiffOn ℝ 2 (u ∘ exchangeMap c) thricePuncturedSphereReal :=
    hu.comp (contDiff_exchangeMap c).contDiffOn fun w hw ↦
      (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ w).2 hw
  have h := integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
    ω hH hHs hv hR
  have hS : {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} = thricePuncturedSphereReal :=
    Set.ext fun _ ↦ mem_thricePuncturedSphereReal_iff.symm
  rw [hS] at h ⊢
  rw [← integral_floerEnergyDensity_exchangeTruncation_eq ω hH hHs hc₀ hc₁ hu (by linarith),
    ← integral_hamiltonianCurvature_exchangePerturbation_eq ω hH hHs hc₀ hc₁] at h
  rw [h]
  -- The boundary loops of `u ∘ Φ_c` are those of `u` on the recentred ends.
  simp only [Puncture.sum_univ, endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul,
    comp_apply, exchangeMap_cylindricalEndLift c (q := zero) (by decide) (by linarith : 0 ≤ R),
    exchangeMap_cylindricalEndLift c (q := one) (by decide) (by linarith : 0 ≤ R),
    exchangeMap_cylindricalEndLift_inf c (by linarith : (1 : ℝ) ≤ R)]
  ring

/-- **The energy and the actions along the input-exchange family.** If the end Hamiltonians are
bounded, `|H_q| ≤ B_q`, then for every `c ∈ [0, 1]` and `R ≥ 2` the Floer energy of `u` for the
member `c` of the family over the truncation with recentred output end differs from the change of
action `A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) - A_{H_∞}(ℓ^c_∞)` of its boundary loops by at most
`B_0 + B_1 + B_∞`, uniformly in `c` and `R`. -/
theorem abs_integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u z) -
      (ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
          (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  rw [integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation ω hH hHs hc₀ hc₁ hu hR,
    sub_sub_cancel_left, abs_neg]
  -- The curvature along `u` is the curvature of the pair-of-pants datum along `u ∘ Φ_c`.
  have hS : {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} = thricePuncturedSphereReal :=
    Set.ext fun _ ↦ mem_thricePuncturedSphereReal_iff.symm
  rw [hS, integral_hamiltonianCurvature_exchangePerturbation_eq ω hH hHs hc₀ hc₁]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB _ _

/-- **The curvature lower bound along the input-exchange family.** If `u` is continuous on
`S = ℂ ∖ {0, 1}` and `h_q` are functions of time, integrable over one period, with `h_q ≤ H_q` on
the input ends and `H_∞ ≤ h_∞` on the output end, then for every `c ∈ [0, 1]` the integrated
curvature of `K_c` along `u` over `S` is at least `∫₀¹ h_0 + ∫₀¹ h_1 - ∫₀¹ h_∞`. -/
theorem sum_mul_integral_le_setIntegral_hamiltonianCurvature_exchangePerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {h : Puncture → ℝ → ℝ} (hh : ∀ q, IntervalIntegrable (h q) volume 0 1)
    (hhH : ∀ q t x, q.endSign * h q t ≤ q.endSign * H q t x) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContinuousOn u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}) :
    ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, h q t ≤
      ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
  -- The curvature along `u` is the curvature of the pair-of-pants datum along `u ∘ Φ_c`.
  have hv : ContinuousOn (u ∘ exchangeMap c) thricePuncturedSphereReal :=
    hu.comp (contDiff_exchangeMap c).continuous.continuousOn
      fun w hw ↦ (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ w).2 hw
  have hS : {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} = thricePuncturedSphereReal :=
    Set.ext fun _ ↦ mem_thricePuncturedSphereReal_iff.symm
  have hcurv := sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation
    ω hH hHs hh hhH (u := u ∘ exchangeMap c) (by rwa [hS])
  rwa [hS, ← integral_hamiltonianCurvature_exchangePerturbation_eq ω hH hHs hc₀ hc₁] at hcurv

/-- **The one-sided action bound along the input-exchange family.** Let `u` be a map which is
`C²` on `S = ℂ ∖ {0, 1}` and solves the Floer equation `(du - X_K)^{0,1} = 0` for the member
`c ∈ [0, 1]` of the input-exchange family, with almost complex structures `J(z)` tamed by `ω`, on
the truncation with recentred output end, `R ≥ 2`. If `h_q` are functions of time, integrable over
one period, with `h_q ≤ H_q` on the input ends and `H_∞ ≤ h_∞` on the output end, then

`A_{H_∞}(ℓ^c_∞) ≤ A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) - ∫₀¹ h_0 - ∫₀¹ h_1 + ∫₀¹ h_∞`

for the boundary loops `ℓ_q(t) = u(φ_q(R + i t))` and `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))`. The
constant does not depend on `c`. -/
theorem hamiltonianAction_le_add_add_sub_sum_of_exchangePerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {h : Puncture → ℝ → ℝ} (hh : ∀ q, IntervalIntegrable (h q) volume 0 1)
    (hhH : ∀ q t x, q.endSign * h q t ≤ q.endSign * H q t x) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, h q t := by
  -- The energy over the truncation is nonnegative.
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_preimage_exchangeTruncation c R)
    fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have hcurv := sum_mul_integral_le_setIntegral_hamiltonianCurvature_exchangePerturbation
    ω hH hHs hh hhH hc₀ hc₁ hu.continuousOn
  rw [integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation ω hH hHs hc₀ hc₁ hu hR]
    at hE
  linarith

/-- **The action bound along the input-exchange family.** Let `K_c` be the member `c ∈ [0, 1]`
of the input-exchange family of period-one `C¹` Hamiltonians `H_q` with `|H_q| ≤ B_q`, and let `u`
be a map which is `C²` on `S = ℂ ∖ {0, 1}` and solves the Floer equation `(du - X_K)^{0,1} = 0` for
`K_c` on the truncation with recentred output end, `R ≥ 2`, for almost complex structures `J(z)`
tamed by `ω`. Then the action of the output loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` is at most the
sum of the actions of the input loops `ℓ_q(t) = u(φ_q(R + i t))` plus `B_0 + B_1 + B_∞`:

`A_{H_∞}(ℓ^c_∞) ≤ A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) + B_0 + B_1 + B_∞`,

uniformly in `c`. -/
theorem hamiltonianAction_le_add_add_sum_of_exchangePerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {R : ℝ} (hR : 2 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) + ∑ q, B q := by
  have h := hamiltonianAction_le_add_add_sub_sum_of_exchangePerturbation ω hH hHs
    (h := fun q _ ↦ -(q.endSign * B q)) (fun _ ↦ intervalIntegrable_const)
    (endSign_mul_neg_endSign_mul_le hB) hc₀ hc₁ hu hR hJ hfloer
  rwa [sum_endSign_mul_integral_neg_endSign_mul, sub_neg_eq_add] at h

/-- **The one-sided action bound for the limiting actions along the input-exchange family.**
Let `u` be a map which is `C²` on `S = ℂ ∖ {0, 1}` and solves the Floer equation for the member
`c ∈ [0, 1]` of the input-exchange family on `S`, for almost complex structures `J(z)` tamed by
`ω`. If the actions of the input loops `ℓ_q(t) = u(φ_q(R + i t))` and of the output loop
`ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` converge to `a_q` as `R → ∞`, and `h_q` are functions of time,
integrable over one period, with `h_q ≤ H_q` on the input ends and `H_∞ ≤ h_∞` on the output end,
then

`a_∞ ≤ a_0 + a_1 - ∫₀¹ h_0 - ∫₀¹ h_1 + ∫₀¹ h_∞`. -/
theorem le_add_add_sub_sum_of_tendsto_hamiltonianAction_exchangePerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {h : Puncture → ℝ → ℝ} (hh : ∀ q, IntervalIntegrable (h q) volume 0 1)
    (hhH : ∀ q t x, q.endSign * h q t ≤ q.endSign * H q t x) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha₀ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
      (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a zero)))
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a one)))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (a inf))) :
    a inf ≤ a zero + a one - ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, h q t := by
  exact le_of_tendsto_of_tendsto ha ((ha₀.add ha₁).sub_const _) <| eventually_atTop.2
    ⟨2, fun R hR ↦ hamiltonianAction_le_add_add_sub_sum_of_exchangePerturbation ω hH hHs hh hhH
      hc₀ hc₁ hu hR (fun z hz ↦ hJ z (exchangeTruncation_subset c R hz))
      fun z hz ↦ hfloer z (exchangeTruncation_subset c R hz)⟩

/-- **The action bound for the limiting actions along the input-exchange family.** Under the
hypotheses of `SymplecticForm.le_add_add_sub_sum_of_tendsto_hamiltonianAction_exchangePerturbation`,
if moreover `|H_q| ≤ B_q`, then the limiting action of the recentred output end is at most the sum
of the limiting actions of the input ends plus `B_0 + B_1 + B_∞`:

`a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞`,

uniformly in `c ∈ [0, 1]`. -/
theorem le_add_add_sum_of_tendsto_hamiltonianAction_exchangePerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha₀ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
      (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a zero)))
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a one)))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (a inf))) :
    a inf ≤ a zero + a one + ∑ q, B q := by
  have h := le_add_add_sub_sum_of_tendsto_hamiltonianAction_exchangePerturbation ω hH hHs
    (h := fun q _ ↦ -(q.endSign * B q)) (fun _ ↦ intervalIntegrable_const)
    (endSign_mul_neg_endSign_mul_le hB) hc₀ hc₁ hu hJ hfloer ha₀ ha₁ ha
  rwa [sum_endSign_mul_integral_neg_endSign_mul, sub_neg_eq_add] at h

/-! ### The energy over the whole pair of pants -/

/-- **The energy along the input-exchange family.** Let `K_c` be the member `c ∈ [0, 1]` of the
input-exchange family of period-one `C¹` Hamiltonians `H_q`, and let `u` be a map which is `C²` on
`S = ℂ ∖ {0, 1}` and solves the Floer equation `(du - X_K)^{0,1} = 0` for `K_c` on `S`, for almost
complex structures `J(z)` tamed by `ω`. If the actions of the input loops
`ℓ_q(t) = u(φ_q(R + i t))` and of the output loop `ℓ^c_∞(t) = u(c + φ_∞(-R + i t))` converge to
`a_q` as `R → ∞`, then the energy of `u` over `S` is

`E(u) = a_0 + a_1 - a_∞ - ∫_S R_{K_c}(u)`.

In particular the energy is finite. -/
theorem lintegral_floerEnergyDensity_exchangePerturbation_eq (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha₀ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
      (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a zero)))
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a one)))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (a inf))) :
    ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) =
      ENNReal.ofReal (a zero + a one - a inf -
        ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity
    (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set T : ℝ → Set (ℝ × ℝ) := fun R ↦ Complex.equivRealProdCLM.symm ⁻¹' exchangeTruncation c R
  have hTS := preimage_exchangeTruncation_subset c
  have hKc (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) :=
    fun p hp ↦ (contDiffAt_uncurry_exchangePerturbation hH hHs c hp.1 p.2 v).contDiffWithinAt
  have he : ContinuousOn e thricePuncturedSphereReal :=
    ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal (hu.of_le one_le_two)
      (hKc 1) (hKc Complex.I)
  -- The lower integrals over `T R` are the measures of `T R` for the density `ofReal ∘ e`, and the
  -- truncations increase to `S`, so these measures converge to the energy over `S`.
  have hlim := tendsto_measure_iUnion_atTop
    (μ := volume.withDensity fun z ↦ ENNReal.ofReal (e z)) (s := T)
    fun R R' hRR' ↦ preimage_mono (exchangeTruncation_mono c hRR')
  rw [iUnion_preimage_exchangeTruncation,
    withDensity_apply _ isOpen_thricePuncturedSphereReal.measurableSet] at hlim
  refine tendsto_nhds_unique hlim ?_
  -- On `T R`, `R ≥ 2`, the energy is the change of action minus the curvature over `S`.
  refine ((ENNReal.continuous_ofReal.tendsto _).comp
    (((ha₀.add ha₁).sub ha).sub_const _)).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with R hR
  have hTc : IsCompact (T R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_exchangeTruncation c R)
  simp only [Function.comp_apply]
  rw [withDensity_apply _ (measurableSet_preimage_exchangeTruncation c R),
    ← ofReal_integral_eq_lintegral_ofReal ((he.mono (hTS R)).integrableOn_compact hTc)
    (ae_restrict_of_forall_mem (measurableSet_preimage_exchangeTruncation c R) fun z hz ↦
      ω.floerEnergyDensity_nonneg (hJ z (hTS R hz)) (hfloer z (hTS R hz))),
    integral_floerEnergyDensity_exchangePerturbation_exchangeTruncation ω hH hHs hc₀ hc₁ hu hR]

/-- **The one-sided energy bound along the input-exchange family.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_exchangePerturbation_eq`, if `h_q` are functions of
time, integrable over one period, with `h_q ≤ H_q` on the input ends and `H_∞ ≤ h_∞` on the output
end, then the energy of `u` over `S` satisfies

`E(u) ≤ a_0 + a_1 - a_∞ - ∫₀¹ h_0 - ∫₀¹ h_1 + ∫₀¹ h_∞`,

with a constant that does not depend on `c`. -/
theorem lintegral_floerEnergyDensity_exchangePerturbation_le_sub_sum (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {h : Puncture → ℝ → ℝ} (hh : ∀ q, IntervalIntegrable (h q) volume 0 1)
    (hhH : ∀ q t x, q.endSign * h q t ≤ q.endSign * H q t x) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha₀ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
      (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a zero)))
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a one)))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (a inf))) :
    ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) ≤
      ENNReal.ofReal (a zero + a one - a inf - ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, h q t) := by
  rw [lintegral_floerEnergyDensity_exchangePerturbation_eq ω hH hHs hc₀ hc₁ hu hJ hfloer ha₀ ha₁
    ha]
  exact ENNReal.ofReal_le_ofReal (sub_le_sub_left
    (sum_mul_integral_le_setIntegral_hamiltonianCurvature_exchangePerturbation
      ω hH hHs hh hhH hc₀ hc₁ hu.continuousOn) _)

/-- **The energy bound along the input-exchange family.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_exchangePerturbation_eq`, if moreover `|H_q| ≤ B_q`,
then the energy of `u` over `S` is at most `a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞`, uniformly in
`c ∈ [0, 1]`. -/
theorem lintegral_floerEnergyDensity_exchangePerturbation_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha₀ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
      (zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a zero)))
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
      (one.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (a one)))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
      (↑c + inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) atTop (𝓝 (a inf))) :
    ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) ≤
      ENNReal.ofReal (a zero + a one - a inf + ∑ q, B q) := by
  have h := lintegral_floerEnergyDensity_exchangePerturbation_le_sub_sum ω hH hHs
    (h := fun q _ ↦ -(q.endSign * B q)) (fun _ ↦ intervalIntegrable_const)
    (endSign_mul_neg_endSign_mul_le hB) hc₀ hc₁ hu hJ hfloer ha₀ ha₁ ha
  rwa [sum_endSign_mul_integral_neg_endSign_mul, sub_neg_eq_add] at h

end SymplecticForm

end TauCeti
