/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Associativity
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Asymptotic
import TauCeti.Topology.Separation.Basic

/-!
# The energy identity along the associativity family

The associativity of the pair-of-pants product on homology compares the two compositions
`(x₁ x₂) x₃` and `x₁ (x₂ x₃)` through the one-parameter family of Floer data
`K_τ = TauCeti.Floer.associativityPerturbation H Hout G G' L τ`, `τ ∈ ℝ`, on spheres with three
moving input ends: for `τ ≤ 0` and `τ ≥ 1` it is a plumbed four-punctured sphere whose neck carries
a scaled intermediate Hamiltonian, and for `0 ≤ τ ≤ 1` it is the datum of the input ends alone.
Finiteness of the counts below each energy level over that family, and compactness of its moduli
spaces, need the energy identity of its maps with bounds uniform in `τ` and in the neck length.
This file proves it for a manifold target.

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold, let the Hamiltonians be
bounded, period-one and `C¹`, `|H i| ≤ B i`, `|Hout| ≤ Bout`, `|G| ≤ BG`, `|G'| ≤ BG'`, and let
`L > 4`. Write `c_i` and `a_i` for the centers and scales of the input ends at `τ`
(`TauCeti.Floer.associativityCenter`, `TauCeti.Floer.associativityScale`, of plumbing factor
`e^{-2πL} / 4`). For a map `u` which is `C¹` on the sphere minus its punctures, the plane minus the
centers `c_i`, with integrable energy and area densities, and whose loops along the input ends
`t ↦ u(c_i + a_i φ₀(R + i t))` and the output end `t ↦ u(φ_∞(-R + i t))` converge pointwise to
loops `x i` and `xout` as `R → ∞`,

`∫ E = ∫ u^*ω + (∑ i, ∫₀¹ H_i(t, x_i(t)) dt - ∫₀¹ Hout(t, xout(t)) dt) - ∫ R_{K_τ}(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_associativityPerturbation`), at every
`τ`. Since the integrated curvature of the family is at most `∑ i, B i + Bout + 2 (BG + BG')`
(`TauCeti.SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_associativityPerturbation_le`), the
energy differs from its topological part by at most that constant, uniformly in `τ` and `L`
(`SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_associativityPerturbation_sub_le`),
and for a solution of the Floer equation with tame almost complex structures the topological part
is at least its negative
(`SmoothTwoForm.IsNondegenerate.neg_sum_add_le_integral_add_of_associativityPerturbation`).

On `[0, 1]` the identity is that of the sphere with moving input ends,
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation`. Outside,
it is that of the whole plumbed four-punctured sphere,
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`, read in the
coordinates of moving input ends
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation_update_smul`): the
input ends of the inserted pair of pants, pushed forward by the plumbing map, are the input ends
of centers `c_q`, `ψ(1)` and scales `f`, `-f`, the remaining input of the receiving pair of pants
is the end of center `c_r` and scale `2 b_r`, and the neck contributes no boundary term. For
`τ ≥ 1` the inputs of the plumbed sphere of `x₁ (x₂ x₃)` are those of the configuration relabelled
by `finRotate 3`, which does not change the sum over the inputs.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `IsNondegenerate.integral_floerEnergyDensity_associativityPerturbation`: the energy identity on
  the whole sphere, at the asymptotic loops, for every member of the family.
* `IsNondegenerate.abs_integral_floerEnergyDensity_associativityPerturbation_sub_le`: the energy
  bound, uniform in `τ` and in the neck length.
* `IsNondegenerate.neg_sum_add_le_integral_add_of_associativityPerturbation`: the lower bound on
  the topological energy of a Floer solution.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product and the energy estimates
  over its families.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E E' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace E']
  {I : ModelWithCorners ℝ E E'} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M}

variable [FiniteDimensional ℝ E]

variable {H : Fin 3 → ℝ → M → ℝ} {Hout G G' : ℝ → M → ℝ} {L : ℝ}

/-- Before the associativity path, the family is the plumbed datum of `(x₁ x₂) x₃` with a scaled
neck, whose energy identity is that of the plumbed sphere. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_associativityPerturbation_of_neg
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G)) (hL : 4 < L) {τ : ℝ} (hτ : τ < 0)
    {B : Fin 3 → ℝ} {Bout BG : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) (hBG : ∀ t x, |G t x| ≤ BG) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    {x : Fin 3 → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
          zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}) :
    ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}, ω.floerEnergyDensity
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout t)) -
        ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}, ω.hamiltonianCurvature
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            1)
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z) := by
  have hL₀ : 0 ≤ L := by linarith
  obtain ⟨Ha, Hb, rfl, rfl⟩ : ∃ Ha Hb : Puncture → ℝ → M → ℝ,
      H = ![Ha zero, Ha one, Hb one] ∧ Hout = Hb inf :=
    ⟨fun p ↦ if p = zero then H 0 else H 1, fun p ↦ if p = inf then Hout else H 2,
      by funext i; fin_cases i <;> rfl, rfl⟩
  rw [associativityPerturbation_of_nonpos hL₀ hτ.le] at hE ⊢
  exact hω.integral_floerEnergyDensity_plumbedPerturbation_update_smul (q := zero) (r := one)
    (by decide) (by decide) (by decide)
    (fun p hp ↦ by cases p; exacts [hH 0, hH 1, absurd rfl hp])
    (fun p hp ↦ by cases p; exacts [absurd rfl hp, hH 2, hHout]) hG
    (fun p hp ↦ by cases p; exacts [hHs 0, hHs 1, absurd rfl hp])
    (fun p hp ↦ by cases p; exacts [absurd rfl hp, hHs 2, hHouts]) hGs hL (smoothTransition (-τ))
    (Ba := fun p ↦ if p = zero then B 0 else B 1) (Bb := fun p ↦ if p = inf then Bout else B 2)
    (fun p hp ↦ by cases p; exacts [hB 0, hB 1, absurd rfl hp])
    (fun p hp ↦ by cases p; exacts [absurd rfl hp, hB 2, hBout]) hBG
    (associativityCenter_eq_plumbingMap_of_nonpos hτ.le)
    (associativityScale_eq_plumbingFactor_of_nonpos hτ.le) rfl hu hx hxout hE hA

/-- After the associativity path, the family is the plumbed datum of `x₁ (x₂ x₃)` with a scaled
neck, whose input ends are those of the configuration relabelled by `finRotate 3`. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_associativityPerturbation_of_one_lt
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (hG' : Periodic G' 1)
    (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G')) (hL : 4 < L) {τ : ℝ} (hτ : 1 < τ)
    {B : Fin 3 → ℝ} {Bout BG' : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) (hBG' : ∀ t x, |G' t x| ≤ BG') {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    {x : Fin 3 → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
          zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}) :
    ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}, ω.floerEnergyDensity
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout t)) -
        ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}, ω.hamiltonianCurvature
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            1)
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z) := by
  have hL₀ : 0 ≤ L := by linarith
  obtain ⟨Ha, Hb, rfl, rfl⟩ : ∃ Ha Hb : Puncture → ℝ → M → ℝ,
      H = ![Hb zero, Ha zero, Ha one] ∧ Hout = Hb inf :=
    ⟨fun p ↦ if p = zero then H 1 else H 2, fun p ↦ if p = inf then Hout else H 0,
      by funext i; fin_cases i <;> rfl, rfl⟩
  have hS : {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i} =
      {z : ℝ × ℝ | ∀ j, Complex.equivRealProdCLM.symm z ≠
        (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ ∘ finRotate 3) j} := by
    ext z
    exact (finRotate 3).forall_congr_right.symm
  rw [associativityPerturbation_of_one_le hL₀ hτ.le, hS] at hE ⊢
  rw [hS] at hu hA
  rw [hω.integral_floerEnergyDensity_plumbedPerturbation_update_smul (q := one) (r := zero)
    (by decide) (by decide) (by decide)
    (fun p hp ↦ by cases p; exacts [hH 1, hH 2, absurd rfl hp])
    (fun p hp ↦ by cases p; exacts [hH 0, absurd rfl hp, hHout]) hG'
    (fun p hp ↦ by cases p; exacts [hHs 1, hHs 2, absurd rfl hp])
    (fun p hp ↦ by cases p; exacts [hHs 0, absurd rfl hp, hHouts]) hG's hL
    (smoothTransition (τ - 1))
    (Ba := fun p ↦ if p = zero then B 1 else B 2) (Bb := fun p ↦ if p = inf then Bout else B 0)
    (fun p hp ↦ by cases p; exacts [hB 1, hB 2, absurd rfl hp])
    (fun p hp ↦ by cases p; exacts [hB 0, absurd rfl hp, hBout]) hBG'
    (associativityCenter_comp_finRotate_of_one_le hτ.le)
    (associativityScale_comp_finRotate_of_one_le hτ.le)
    (H := ![Hb zero, Ha zero, Ha one] ∘ finRotate 3) (by funext j; fin_cases j <;> rfl) hu
    (x := x ∘ finRotate 3) (fun j t ↦ hx (finRotate 3 j) t) hxout hE hA]
  simp only [comp_apply]
  rw [Equiv.sum_comp (finRotate 3)
    (fun i ↦ ∫ t in (0 : ℝ)..1, (![Hb zero, Ha zero, Ha one] : Fin 3 → ℝ → M → ℝ) i t (x i t))]

/-- **The energy identity along the associativity family, for a manifold target.** Let `K_τ` be
the member at `τ` of the associativity family `associativityPerturbation H Hout G G' L τ`, for
bounded period-one `C¹` Hamiltonians `H i`, `Hout`, `G` and `G'` on a finite-dimensional manifold
with a nondegenerate two-form and a neck length `L > 4`, with components `K_s(z) = K_τ(z)(1)` and
`K_t(z) = K_τ(z)(i)` in the global coordinate `z = s + i t` of `ℂ`. Let `c_i` and `a_i` be the
centers and scales of the input ends of the configuration at `τ`, those of
`associativityCenter` and `associativityScale` of plumbing factor `e^{-2πL} / 4`. Let `u` be `C¹`
on the sphere minus its punctures, the points of the plane other than the centers `c_i`, with
Floer energy density and symplectic area density integrable there. Suppose the loops
`t ↦ u(c_i + a_i φ₀(R + i t))` along the circles of the input end `i` converge pointwise to loops
`x i`, and the loops `t ↦ u(φ_∞(-R + i t))` along the circles of the output end converge pointwise
to a loop `xout`, as `R → ∞`. Then

`∫ E = ∫ u^*ω + (∑ i, ∫₀¹ H_i(t, x_i(t)) dt - ∫₀¹ Hout(t, xout(t)) dt) - ∫ R_{K_τ}(u)`,

the integrals over the sphere minus its punctures, at every `τ`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_associativityPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G)) (hG' : Periodic G' 1)
    (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G')) (hL : 4 < L) (τ : ℝ)
    {B : Fin 3 → ℝ} {Bout BG BG' : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) (hBG : ∀ t x, |G t x| ≤ BG)
    (hBG' : ∀ t x, |G' t x| ≤ BG') {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    {x : Fin 3 → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
          zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}) :
    ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}, ω.floerEnergyDensity
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout t)) -
        ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}, ω.hamiltonianCurvature
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            1)
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z) := by
  rcases lt_or_ge τ 0 with hτ | hτ₀
  · exact hω.integral_floerEnergyDensity_associativityPerturbation_of_neg hH hHs hHout hHouts hG
      hGs hL hτ hB hBout hBG hu hx hxout hE hA
  rcases le_or_gt τ 1 with hτ₁ | hτ
  · -- Along the path, the family is the datum of the moving input ends.
    have hf₀ : 0 < Real.exp (-(2 * π * L)) / 4 := by positivity
    have hf₁ : Real.exp (-(2 * π * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
    rw [associativityPerturbation_of_mem_Icc ⟨hτ₀, hτ₁⟩] at hE ⊢
    exact hω.integral_floerEnergyDensity_puncturedSpherePerturbation hH hHs hHout hHouts
      (associativityScale_ne_zero hf₀ τ)
      (pairwise_add_le_norm_associativityCenter_sub hf₀.le (by linarith) τ)
      (norm_associativityCenter_add_le hf₀.le (by linarith) τ) hB hBout hu hx hxout hE hA
  · exact hω.integral_floerEnergyDensity_associativityPerturbation_of_one_lt hH hHs hHout hHouts
      hG' hG's hL hτ hB hBout hBG' hu hx hxout hE hA

/-- **The energy bound along the associativity family, for a manifold target.** Under the
hypotheses of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_associativityPerturbation`,
the Floer energy differs from the symplectic area plus the Hamiltonian terms at the asymptotic
loops by at most `∑ i, B i + Bout + 2 (BG + BG')`, uniformly in `τ` and in the neck length
`L > 4`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_associativityPerturbation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G)) (hG' : Periodic G' 1)
    (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G')) (hL : 4 < L) (τ : ℝ)
    {B : Fin 3 → ℝ} {Bout BG BG' : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) (hBG : ∀ t x, |G t x| ≤ BG)
    (hBG' : ∀ t x, |G' t x| ≤ BG') {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    {x : Fin 3 → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
          zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}) :
    |(∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i}, ω.floerEnergyDensity
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z) -
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout t))| ≤
      ∑ i, B i + Bout + 2 * (BG + BG') := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_associativityPerturbation hH hHs hHout hHouts hG hGs hG' hG's
    hL τ hB hBout hBG hBG' hu hx hxout hE hA, hsub, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_associativityPerturbation_le hH hHs hHout hHouts hG
    hGs hG' hG's hL τ hB hBout hBG hBG' u _

/-- **The topological energy of a solution along the associativity family is bounded below, for a
manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on the sphere minus its
punctures for the member `K` of the associativity family at `τ` and almost complex structures
`J z` on the tangent spaces `T_{u(z)} M` tamed by the two-form, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_associativityPerturbation`. Since its
energy is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic loops is at
least `-(∑ i, B i + Bout + 2 (BG + BG'))`, whatever `τ` and the neck length `L > 4`. -/
theorem IsNondegenerate.neg_sum_add_le_integral_add_of_associativityPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G)) (hG' : Periodic G' 1)
    (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G')) (hL : 4 < L) (τ : ℝ)
    {B : Fin 3 → ℝ} {Bout BG BG' : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) (hBG : ∀ t x, |G t x| ≤ BG)
    (hBG' : ∀ t x, |G' t x| ≤ BG') {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    {x : Fin 3 → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
        associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
          zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) u)
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i})
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i},
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            1)
          (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z).toLinearMap) :
    -(∑ i, B i + Bout + 2 * (BG + BG')) ≤
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
          associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hout t (xout t)) := by
  have hE₀ := setIntegral_nonneg (μ := volume)
    (isOpen_forall_ne Complex.equivRealProdCLM.symm.continuous).measurableSet fun z hz ↦
    floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (hω.abs_integral_floerEnergyDensity_associativityPerturbation_sub_le hH hHs hHout hHouts hG hGs
      hG' hG's hL τ hB hBout hBG hBG' hu hx hxout hE hA)).2
  linarith

end TauCeti.SmoothTwoForm
